"""
Simple USB camera viewer (re-created):
- Main window = controls (dark modern pastel theme).
- Video window (resizable) opens only after user opens a camera.
- Probes common resolutions for selected camera (background).
- Draw modes: rounded-rectangle and arrow. Overlays can be moved, deleted,
  recolored and are saved into snapshots.
- Minimal useful settings: resolution selection, brightness & contrast,
  color picker, snapshot, open/close camera.
"""
import cv2
import tkinter as tk
from tkinter import ttk, colorchooser
from PIL import Image, ImageTk, ImageDraw, ImageFont
import threading
import time
import datetime
from typing import List, Tuple, Optional
import math
from concurrent.futures import ThreadPoolExecutor, as_completed
import subprocess
import platform
import json
import os
import sys

# Try to mute OpenCV/driver logs (best-effort for multiple OpenCV versions)
try:
    # OpenCV >= 4.5
    cv2.setLogLevel(cv2.LOG_LEVEL_ERROR)
except Exception:
    try:
        # alternative API
        cv2.utils.logging.setLogLevel(cv2.utils.logging.LOG_LEVEL_ERROR)
    except Exception:
        # best-effort: ignore if not available
        pass

# ---------- Helper / constants ----------
PALETTE_BG = "#0f1720"     # very dark
PALETTE_PANEL = "#111827"  # panel
PALETTE_TEXT = "#e6eef6"   # pale text
PALETTE_ACCENT = "#7dd3fc" # pastel cyan
PALETTE_BTN = "#1f2937"
COMMON_RESOLUTIONS = [(3840,2160),(2560,1440),(1920,1080),(1280,720),(1024,768),(800,600),(640,480),(320,240)]

# ---------- Main application ----------
class USBCameraApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("PyCam — Controls")
        self.root.configure(bg=PALETTE_BG)
        self.root.geometry("760x480")

        # app state
        self.camera_index = None
        self.cap = None
        self.reader_thread = None
        self._reader_running = False
        self._latest_frame = None
        self._frame_lock = threading.Lock()
        self._capture_size = (640, 480)  # actual capture resolution requested
        self._display_size = (640, 480)  # last shown size in video window
        # overlays: (mode: 'rrect'|'arrow', p1(x,y), p2(x,y), (r,g,b))
        self.overlays: List[Tuple[str, Tuple[int,int], Tuple[int,int], Tuple[int,int,int]]] = []
        self.selected_overlay: Optional[int] = None
        self._moving = False
        self._move_last = (0,0)

        # image adjustments
        self.brightness = 0
        self.contrast = 1.0
        # focus controls
        self.auto_focus_var = tk.BooleanVar(value=True)
        self.focus_value = 0  # manual focus value (0..255)
        self._focus_supported = False

        # UI variables
        self.cam_var = tk.StringVar(value="None")
        self.res_var = tk.StringVar(value="640x480")
        self.mode_var = tk.StringVar(value="none")  # draw mode
        self.swatch_color = (0, 200, 120)
        # picture manipulation state (must exist before building UI that references them)
        self.mirror = tk.BooleanVar(value=False)
        self.rotate_deg = tk.IntVar(value=0)          # 0,90,180,270
        self.zoom_factor = tk.DoubleVar(value=1.0)    # 1.0 .. 3.0
        # panning state (pixels offset from center when zoom > 1)
        self.pan_offset = [0, 0]
        self._pan_start = None
        # FPS tracking
        self._frame_counter = 0
        self._fps_last_time = time.time()
        self._current_fps = 0
        # snapshot directory
        self.snapshot_dir = os.path.join(os.getcwd(), "snapshots")
        try:
            os.makedirs(self.snapshot_dir, exist_ok=True)
        except Exception:
            pass
        # build controls after vars exist
        self._build_controls()

        # video window references (created when camera opened)
        self.video_win = None
        self.video_label = None

        # initial camera scan: defer async scan so UI shows instantly
        self._cam_display_map = {}
        self._scanning_cams = False
        self._scanning_res = False
        self.root.after(150, self._scan_cameras_async)

        # UI throttling / frame dropping
        self._ui_busy = False
        self._last_ui_time = 0.0
        self._ui_interval_ms = 33  # ~30 FPS UI update cap
        # last display sizing/scale (for coordinate transforms)
        self._last_disp_size = (self._capture_size[0], self._capture_size[1])
        self._last_scale = 1.0
        # top-left origin of the displayed image inside the label (when centered)
        self._last_img_origin = (0, 0)
        # settings persistence additions
        self._camera_uid_map = {}
        self._current_camera_uid = None
        self._pending_select_cam_uid: Optional[str] = None
        # settings persistence
        # base directory (exe folder when frozen, script folder otherwise)
        self._base_dir = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
        # asset directory (PyInstaller one-file extracts to sys._MEIPASS)
        self._asset_dir = getattr(sys, "_MEIPASS", self._base_dir)
        # settings persistence path
        self._settings_path = os.path.join(self._base_dir, "settings.json")
        self._pending_select_cam_idx: Optional[int] = None
        self._pending_select_res: Optional[str] = None
        # per-camera known resolutions
        self._known_resolutions: dict[str, list[str]] = {}
        # last scanned cameras snapshot for persistence
        self._last_scanned_cameras = []
        # per-camera adjustments (persisted)
        self._camera_adjustments: dict[str, dict] = {}
        # spinner busy counter
        self._busy_ops = 0
        # log buffer
        self._logs: list[str] = []
        self._load_settings()
        # apply loaded defaults to tk variables before building controls
        try:
            self.rotate_deg.set(int(getattr(self, "rotate_deg").get()))
        except Exception:
            pass
        # build UI
        # ensure settings saved on app exit
        try:
            self.root.protocol("WM_DELETE_WINDOW", self._on_root_close)
        except Exception:
            pass
        # force show main window (some environments start hidden)
        self.root.after(50, self._ensure_root_visible)

        # apply icon to main window if available
        try:
            icon_file = os.path.join(self._asset_dir, "webcam.ico")
            if os.path.isfile(icon_file):
                try:
                    self.root.iconbitmap(icon_file)  # Windows ICO
                except Exception:
                    try:
                        ico_img = Image.open(icon_file)
                        self.root.iconphoto(True, ImageTk.PhotoImage(ico_img))
                    except Exception:
                        pass
        except Exception:
            pass

    def _ensure_root_visible(self):
        try:
            if not self.root.winfo_viewable():
                self.root.deiconify()
            self.root.update_idletasks()
            self.root.lift()
        except Exception:
            pass

    # ---------- UI building ----------
    def _build_controls(self):
        pad = 10
        top = tk.Frame(self.root, bg=PALETTE_PANEL, padx=12, pady=10)
        top.pack(fill="x", padx=12, pady=(12,6))

        tk.Label(top, text="Camera:", fg=PALETTE_TEXT, bg=PALETTE_PANEL).grid(row=0, column=0, sticky="w")
        # make camera list ~333px (approx chars for default Tk font)
        self.cam_cb = ttk.Combobox(top, textvariable=self.cam_var, values=[], width=45, state="readonly")
        self.cam_cb.grid(row=0, column=1, padx=(6,12), sticky="we")
        self.cam_cb.bind("<<ComboboxSelected>>", lambda e: self._on_camera_select())
        tk.Label(top, text="Resolution:", fg=PALETTE_TEXT, bg=PALETTE_PANEL).grid(row=1, column=0, sticky="w", pady=(8,0))
        self.res_cb = ttk.Combobox(top, textvariable=self.res_var, values=[], width=20, state="readonly")
        self.res_cb.grid(row=1, column=1, padx=(6,12), sticky="w", pady=(8,0))
        self.res_cb.bind("<<ComboboxSelected>>", lambda e: self._on_resolution_select())
        self.open_btn = tk.Button(top, text="Open", bg=PALETTE_BTN, fg=PALETTE_TEXT, command=self._toggle_camera)
        self.open_btn.grid(row=0, column=2, padx=6, sticky="w")
        ttk.Button(top, text="Rescan", command=self._scan_cameras_async).grid(row=0, column=3, padx=6, sticky="w")
        ttk.Button(top, text="Probe Res", command=self._probe_resolutions_async).grid(row=0, column=4, padx=6, sticky="w")
        # progress bars on the same row (hidden by default)
        # self.scan_prog = ttk.Progressbar(top, mode="indeterminate", length=70)
        # self.scan_prog.grid(row=0, column=7, padx=(4,0))
        # self.scan_prog.grid_remove()
        # self.scan_lbl = tk.Label(top, text="CAM", fg=PALETTE_TEXT, bg=PALETTE_PANEL)
        # self.scan_lbl.grid(row=0, column=8, padx=(2,0))
        # self.scan_lbl.grid_remove()
        # self.res_prog = ttk.Progressbar(top, mode="indeterminate", length=70)
        # self.res_prog.grid(row=0, column=9, padx=(4,0))
        # self.res_prog.grid_remove()
        # self.res_lbl = tk.Label(top, text="RES", fg=PALETTE_TEXT, bg=PALETTE_PANEL)
        # self.res_lbl.grid(row=0, column=10, padx=(2,0))
        # self.res_lbl.grid_remove()
        # adjust Snapshot button column to avoid overlap
        # Snapshot moved below manipulation boxes

        # Middle: adjustments and draw options
        mid = tk.Frame(self.root, bg=PALETTE_BG, padx=12, pady=8)
        mid.pack(fill="both", expand=False, padx=12, pady=(6,12))

        # Adjustments: brightness and contrast
        adj_frame = tk.Frame(mid, bg=PALETTE_PANEL, padx=10, pady=8)
        adj_frame.pack(side="left", anchor="n", padx=(0,12))
        tk.Label(adj_frame, text="Adjustments", bg=PALETTE_PANEL, fg=PALETTE_TEXT).pack(anchor="w")
        b_frame = tk.Frame(adj_frame, bg=PALETTE_PANEL)
        b_frame.pack(anchor="w", pady=(6,0))
        tk.Label(b_frame, text="Brightness", bg=PALETTE_PANEL, fg=PALETTE_TEXT).grid(row=0, column=0, sticky="w")
        self.bright_s = tk.Scale(b_frame, from_=-100, to=100, orient="horizontal", length=200, bg=PALETTE_PANEL, fg=PALETTE_TEXT, command=self._on_brightness)
        self.bright_s.set(self.brightness)
        self.bright_s.grid(row=0, column=1, padx=6)
        tk.Label(b_frame, text="Contrast", bg=PALETTE_PANEL, fg=PALETTE_TEXT).grid(row=1, column=0, sticky="w")
        self.contrast_s = tk.Scale(b_frame, from_=50, to=200, orient="horizontal", length=200, bg=PALETTE_PANEL, fg=PALETTE_TEXT, command=self._on_contrast)
        self.contrast_s.set(int(self.contrast * 100))
        self.contrast_s.grid(row=1, column=1, padx=6)
        # Auto-focus checkbox and manual focus slider (only enabled when camera supports it)
        tk.Label(b_frame, text="Auto Focus", bg=PALETTE_PANEL, fg=PALETTE_TEXT).grid(row=2, column=0, sticky="w", pady=(8,0))
        self.af_cb = tk.Checkbutton(b_frame, text="", variable=self.auto_focus_var, bg=PALETTE_PANEL, fg=PALETTE_TEXT, command=self._on_autofocus_toggle)
        self.af_cb.grid(row=2, column=1, sticky="w", pady=(8,0))
        tk.Label(b_frame, text="Focus", bg=PALETTE_PANEL, fg=PALETTE_TEXT).grid(row=3, column=0, sticky="w")
        self.focus_s = tk.Scale(b_frame, from_=0, to=255, orient="horizontal", length=200, bg=PALETTE_PANEL, fg=PALETTE_TEXT, command=self._on_focus_change)
        self.focus_s.set(self.focus_value)
        self.focus_s.grid(row=3, column=1, padx=6, pady=(0,6))
        # by default disabled until camera open/probe reveals support
        self.focus_s.config(state="disabled")
        self.af_cb.config(state="disabled")
        # focus slider hints (far/near)
        hints = tk.Frame(b_frame, bg=PALETTE_PANEL)
        hints.grid(row=4, column=1, sticky="we")
        tk.Label(hints, text="∞ Far", bg=PALETTE_PANEL, fg=PALETTE_TEXT).pack(side="left")
        tk.Label(hints, text="Near", bg=PALETTE_PANEL, fg=PALETTE_TEXT).pack(side="right")
        # Reset adjustments
        tk.Button(adj_frame, text="Reset Adjust", bg=PALETTE_BTN, fg=PALETTE_TEXT,
                  command=self._reset_adjustments).pack(anchor="w", pady=(8,0))

        # Picture manipulation box
        pic_frame = tk.Frame(mid, bg=PALETTE_PANEL, padx=10, pady=8)
        pic_frame.pack(side="left", anchor="n", padx=(12,0))
        tk.Label(pic_frame, text="Picture", bg=PALETTE_PANEL, fg=PALETTE_TEXT).pack(anchor="w")
        tk.Checkbutton(pic_frame, text="Mirror", variable=self.mirror, bg=PALETTE_PANEL, fg=PALETTE_TEXT,
                       command=lambda: (self._update_video_frame(), self._save_camera_profile(), self._save_settings())).pack(anchor="w")
        tk.Label(pic_frame, text="Rotate", bg=PALETTE_PANEL, fg=PALETTE_TEXT).pack(anchor="w", pady=(6,0))
        rot_box = ttk.Combobox(pic_frame, state="readonly", values=["0","90","180","270"], width=5,
                               textvariable=self.rotate_deg)
        rot_box.pack(anchor="w")
        rot_box.bind("<<ComboboxSelected>>", lambda e: (self._update_video_frame(), self._save_camera_profile(), self._save_settings()))
        tk.Label(pic_frame, text="Zoom", bg=PALETTE_PANEL, fg=PALETTE_TEXT).pack(anchor="w", pady=(6,0))
        zoom_scale = tk.Scale(pic_frame, from_=1.0, to=3.0, resolution=0.1, orient="horizontal", length=140,
                              bg=PALETTE_PANEL, fg=PALETTE_TEXT,
                              command=lambda v: (self.zoom_factor.set(float(v)), self._update_video_frame(), self._save_camera_profile(), self._save_settings()))
        zoom_scale.set(self.zoom_factor.get())
        zoom_scale.pack(anchor="w")
        # Snapshot button below middle area
        snap_container = tk.Frame(self.root, bg=PALETTE_BG)
        snap_container.pack(fill="x", padx=12, pady=(0,4))
        btn_row = tk.Frame(snap_container, bg=PALETTE_BG)
        btn_row.pack(anchor="w")
        tk.Button(btn_row, text="Snapshot", bg=PALETTE_BTN, fg=PALETTE_TEXT,
                  width=12, height=2, command=self._snapshot).pack(side="left", padx=(0,8))
        tk.Button(btn_row, text="Open Folder", bg=PALETTE_BTN, fg=PALETTE_TEXT,
                  width=12, height=2, command=self._open_snapshot_folder).pack(side="left")

        # Draw options
        draw_frame = tk.Frame(mid, bg=PALETTE_PANEL, padx=10, pady=8)
        draw_frame.pack(side="left", anchor="n")
        tk.Label(draw_frame, text="Draw (click-drag)", bg=PALETTE_PANEL, fg=PALETTE_TEXT).pack(anchor="w")
        modes = [("None", "none"), ("Rectangle", "rect"), ("Arrow", "arrow")]
        for i,(t,v) in enumerate(modes):
            tk.Radiobutton(draw_frame, text=t, variable=self.mode_var, value=v, bg=PALETTE_PANEL, fg=PALETTE_TEXT, selectcolor=PALETTE_PANEL).pack(anchor="w")
        # color swatch
        sw = tk.Frame(draw_frame, bg=PALETTE_PANEL)
        sw.pack(anchor="w", pady=(8,0))
        tk.Label(sw, text="Color:", bg=PALETTE_PANEL, fg=PALETTE_TEXT).grid(row=0, column=0)
        self.sw_btn = tk.Button(sw, bg=self._colhex(self.swatch_color), width=3, command=self._pick_color)
        self.sw_btn.grid(row=0, column=1, padx=6)
        # overlay controls
        ovf = tk.Frame(draw_frame, bg=PALETTE_PANEL)
        ovf.pack(anchor="w", pady=(8,0))
        tk.Button(ovf, text="Clear Overlays", command=self._clear_overlays).pack(side="left", padx=(0,6))

        # Footer: instructions
        footer = tk.Label(self.root, text="Select camera → Probe Res → choose resolution → Open Camera. Draw modes shown on video window.",
                          bg=PALETTE_BG, fg=PALETTE_TEXT)
        footer.pack(fill="x", padx=12, pady=(0,0))
        # Bottom status bar
        self.status_bar = tk.Frame(self.root, bg=PALETTE_PANEL)
        self.status_bar.pack(fill="x", side="bottom", padx=0, pady=0)
        self.status_lbl = tk.Label(self.status_bar, text="Idle", bg=PALETTE_PANEL, fg=PALETTE_TEXT, anchor="w")
        self.status_lbl.pack(fill="x", padx=8, pady=6, side="left", expand=True)
        # spinner (hidden by default)
        self.spinner = ttk.Progressbar(self.status_bar, mode="indeterminate", length=80)
        # logs toggle button (right side)
        self.log_btn = tk.Button(self.status_bar, text="Logs", bg=PALETTE_BTN, fg=PALETTE_TEXT, command=self._toggle_logs)
        self.log_btn.pack(side="right", padx=6, pady=4)

        # hidden log panel
        self.log_panel = tk.Frame(self.root, bg=PALETTE_PANEL)
        self.log_scroll = tk.Scrollbar(self.log_panel)
        self.log_text = tk.Text(self.log_panel, height=8, bg="#0b1220", fg="#dbe8ff", insertbackground="#dbe8ff", yscrollcommand=self.log_scroll.set)
        self.log_scroll.config(command=self.log_text.yview)
        self.log_scroll.pack(side="right", fill="y")
        self.log_text.pack(side="left", fill="both", expand=True)
        # start hidden; will be packed/unpacked by _toggle_logs

    # --- UI helper methods for progress ---
    def _set_scan_ui(self, active: bool):
        if active and not self._scanning_cams:
            self._scanning_cams = True
            self.status("Scanning cameras...")
            self._spinner_start()
        elif not active and self._scanning_cams:
            self._scanning_cams = False
            self.status("Scan done.")
            self._spinner_stop()

    def _set_res_scan_ui(self, active: bool):
        if active and not self._scanning_res:
            self._scanning_res = True
            self.status("Probing resolutions...")
            self._spinner_start()
        elif not active and self._scanning_res:
            self._scanning_res = False
            self.status("Resolution probe done.")
            self._spinner_stop()

    # ---------- UI callbacks ----------
    def _on_brightness(self, v):
        try:
            self.brightness = int(v)
        except Exception:
            pass
        self._save_camera_profile(); self._save_settings()

    def _on_contrast(self, v):
        try:
            self.contrast = max(0.1, int(v)/100.0)
        except Exception:
            pass
        self._save_camera_profile(); self._save_settings()

    def _pick_color(self):
        init = "#{:02x}{:02x}{:02x}".format(*self.swatch_color)
        res = colorchooser.askcolor(color=init, parent=self.root)
        if res and res[0]:
            self.swatch_color = tuple(int(c) for c in res[0])
            self.sw_btn.config(bg=self._colhex(self.swatch_color))
    def _on_autofocus_toggle(self):
        # toggle autofocus on the opened camera if possible
        if not self.cap:
            return
        try:
            val = 1 if self.auto_focus_var.get() else 0
            # CAP_PROP_AUTOFOCUS is supported on some platforms / drivers
            self.cap.set(cv2.CAP_PROP_AUTOFOCUS, val)
            # if turning autofocus on, disable manual slider
            self.focus_s.config(state="disabled" if self.auto_focus_var.get() else "normal")
            self.status(f"Set autofocus = {self.auto_focus_var.get()}")
        except Exception:
            self.status("Auto-focus not supported by this camera.")
        self._save_camera_profile(); self._save_settings()

    def _on_focus_change(self, v):
        try:
            self.focus_value = int(v)
        except Exception:
            return
        if not self.cap:
            return
        # only set when autofocus is disabled
        if not self.auto_focus_var.get():
            try:
                self.cap.set(cv2.CAP_PROP_FOCUS, self.focus_value)
                self.status(f"Set focus = {self.focus_value}")
            except Exception:
                self.status("Manual focus not supported.")
        self._save_camera_profile(); self._save_settings()

    def _on_resolution_select(self):
        """Apply selected resolution dynamically; reopen device if needed."""
        sel = self.res_var.get()
        try:
            w, h = map(int, sel.split("x"))
        except Exception:
            return
        self._pending_select_res = sel
        self._capture_size = (w, h)
        if not self.cap:
            self._save_settings()
            return
        # try live change
        ok = False
        try:
            self.cap.set(cv2.CAP_PROP_FRAME_WIDTH, w)
            self.cap.set(cv2.CAP_PROP_FRAME_HEIGHT, h)
            time.sleep(0.05)
            aw = int(self.cap.get(cv2.CAP_PROP_FRAME_WIDTH) or 0)
            ah = int(self.cap.get(cv2.CAP_PROP_FRAME_HEIGHT) or 0)
            ok = (aw == w and ah == h)
        except Exception:
            ok = False
        if not ok:
            # reopen camera at new resolution
            idx = self.camera_index if self.camera_index is not None else self._parse_selected_camera_index()
            if idx is not None:
                self._reopen_camera_with(idx, w, h)
        self.status(f"Resolution set to {w}x{h}")
        self._save_settings()

    def _toggle_camera(self):
        if self.cap:
            self._close_camera()
        else:
            self._open_camera()

    def _scan_cameras_async(self):
        # show progress
        self.root.after(0, lambda: self._set_scan_ui(True))
        def task():
            # Fast Windows 11 enumeration (no device opens). Fallback to probe on other OS.
            idxs, names = [], []
            if platform.system().lower().startswith("win"):
                cams = self._enum_win_cameras()  # returns list of (name, instanceId, statusOk)
                if cams:
                    values = []
                    self._cam_display_map = {}
                    self._camera_uid_map = {}
                    camera_list = []
                    for i, (name, inst_id, is_ok) in enumerate(cams):
                        mf = " [MF]" if self._supports_manual_focus(i) else ""
                        display = f"{i} - {name} ({'available' if is_ok else 'unavailable'}){mf}"
                        values.append(display)
                        self._cam_display_map[display] = i
                        self._camera_uid_map[display] = inst_id
                        camera_list.append({
                            "index": i, "uid": inst_id, "name": name,
                            "available": bool(is_ok), "manual_focus": bool(mf != "")
                        })
                    def done():
                        self.cam_cb.configure(values=values)
                        # store scanned cameras to settings
                        self._last_scanned_cameras = camera_list
                        # restore last by UID if possible
                        if self._pending_select_cam_uid:
                            for disp, uid in self._camera_uid_map.items():
                                if uid == self._pending_select_cam_uid:
                                    self.cam_var.set(disp); break
                        if not self.cam_var.get() or self.cam_var.get() not in self._cam_display_map:
                            self.cam_var.set(values[0] if values else "None")
                        # if we have known resolutions for this camera, prefill
                        self._apply_known_resolutions_to_ui()
                        # apply per-camera adjustments if available
                        self._apply_camera_profile_to_ui(self._current_camera_key())
                        self._set_scan_ui(False)
                        self.status(f"Found {len(values)} cameras.")
                        self._save_settings()
                    self.root.after(0, done)
                    return
            # fallback probe (non-Windows or failed)
            try:
                idxs, names = self._get_system_camera_devices()
            except Exception:
                idxs, names = [], []

            # If system returned only names (or nothing), probe indices (0..4) as fallback.
            # This keeps behavior working on systems where v4l2/powershell didn't yield indices.
            probe_range = range(0, 5)
            def probe_index(i):
                try:
                    cap = cv2.VideoCapture(i)
                    if cap and cap.isOpened():
                        try: cap.release()
                        except Exception: pass
                        return str(i)
                except Exception:
                    pass
                return None

            cams = []
            with ThreadPoolExecutor(max_workers=5) as ex:
                futures = {ex.submit(probe_index, i): i for i in probe_range}
                for fut in as_completed(futures):
                    res = fut.result()
                    if res: cams.append(res)
            cams = sorted(cams, key=lambda s: int(s))

            # Build display strings, attach any system names if available
            def update_probed():
                displays = []
                self._cam_display_map = {}
                self._camera_uid_map = {}
                camera_list = []
                sys_names = self._get_system_camera_names()
                for i,num in enumerate(cams):
                    name = sys_names[i] if i < len(sys_names) else ""
                    avail = self._is_index_available(int(num))
                    mf = " [MF]" if self._supports_manual_focus(int(num)) else ""
                    disp_state = "available" if avail else "unavailable"
                    display = f"{num} - {name} ({disp_state}){mf}" if name else f"{num} ({disp_state}){mf}"
                    displays.append(display)
                    self._cam_display_map[display] = int(num)
                    self._camera_uid_map[display] = name or f"idx:{num}"
                    camera_list.append({
                        "index": int(num),
                        "uid": (name or f"idx:{num}"),
                        "name": name,
                        "available": bool(avail),
                        "manual_focus": bool(mf != "")
                    })
                self.cam_cb.configure(values=displays)
                # store scanned cameras to settings
                self._last_scanned_cameras = camera_list
                # apply last camera if known
                if self._pending_select_cam_uid:
                    for disp, uid in self._camera_uid_map.items():
                        if uid == self._pending_select_cam_uid:
                            self.cam_var.set(disp); break
                if not self.cam_var.get() or self.cam_var.get() not in self._cam_display_map:
                    self.cam_var.set(displays[0] if displays else "None")
                self._apply_known_resolutions_to_ui()
                # apply per-camera adjustments if available
                self._apply_camera_profile_to_ui(self._current_camera_key())
                self._set_scan_ui(False)
                self.status(f"Found {len(displays)} cameras.")
                self._save_settings()
            self.root.after(0, update_probed)

        threading.Thread(target=task, daemon=True).start()

    def _on_camera_select(self):
        # apply known resolutions for this camera if we have them
        self._apply_known_resolutions_to_ui()
        # apply stored adjustments for selected camera
        self._apply_camera_profile_to_ui(self._current_camera_key())
        self._save_settings()
        # switch camera dynamically if currently open
        if self.cap:
            self._switch_camera_to_selected()

    def _probe_resolutions_async(self):
        sel = self.cam_var.get()
        # resolve selection -> numeric index (support "index" or "index - name")
        cam_idx = None
        # first try mapping from display map
        try:
            if sel in getattr(self, "_cam_display_map", {}):
                cam_idx = int(self._cam_display_map[sel])
            else:
                cam_idx = int(str(sel).split()[0])
        except Exception:
            self.status("Select a valid camera index first.")
            return
        self._set_res_scan_ui(True)
        def task():
            supported = []
            temp = None
            try:
                temp = cv2.VideoCapture(cam_idx)
                if not temp or not temp.isOpened():
                    self.root.after(0, lambda: (self._update_resolutions([]), self._set_res_scan_ui(False)))
                    return
                for w,h in COMMON_RESOLUTIONS:
                    try:
                        temp.set(cv2.CAP_PROP_FRAME_WIDTH, w)
                        temp.set(cv2.CAP_PROP_FRAME_HEIGHT, h)
                        # single quick read (fast)
                        r,_ = temp.read()
                        if r:
                            actual_w = int(temp.get(cv2.CAP_PROP_FRAME_WIDTH) or 0)
                            actual_h = int(temp.get(cv2.CAP_PROP_FRAME_HEIGHT) or 0)
                            if actual_w==w and actual_h==h:
                                supported.append(f"{w}x{h}")
                    except Exception:
                        pass
            finally:
                if temp:
                    try: temp.release()
                    except Exception: pass
            def done():
                self._update_resolutions(supported)
                # persist the list per camera
                key = self._current_camera_key()
                if key:
                    self._known_resolutions[key] = list(self.res_cb['values'])
                # apply last resolution if known
                if self._pending_select_res and self._pending_select_res in self.res_cb['values']:
                    try:
                        self.res_var.set(self._pending_select_res)
                    except Exception:
                        pass
                self._set_res_scan_ui(False)
                self.status(f"Probe complete ({len(supported)})")
                self._save_settings()
            self.root.after(0, done)
        threading.Thread(target=task, daemon=True).start()
        self.status("Probing resolutions...")

    def _update_resolutions(self, supported: List[str]):
        if supported:
            vals = [s.split()[0] for s in supported]
            self.res_cb['values'] = vals
            # prefer pending last resolution if present
            if self._pending_select_res in vals:
                self.res_var.set(self._pending_select_res)
            else:
                self.res_var.set(vals[0])
            self.status(f"Found {len(vals)} resolutions.")
        else:
            # fallback: allow user-entered resolution
            self.res_cb['values'] = []
            # fall back to the currently requested capture size
            self.res_var.set(f"{self._capture_size[0]}x{self._capture_size[1]}")
            self.status("No resolutions found by probe.")
        # save known list if tied to current camera
        key = self._current_camera_key()
        if key and self.res_cb['values']:
            self._known_resolutions[key] = list(self.res_cb['values'])
        self._save_settings()

    def _open_camera(self):
        sel = self.cam_var.get()
        # resolve selection -> numeric index (support "index" or "index - name")
        cam_idx = None
        # first try mapping from display map
        try:
            if sel in getattr(self, "_cam_display_map", {}):
                cam_idx = int(self._cam_display_map[sel])
            else:
                # fallback: parse leading integer
                cam_idx = int(str(sel).split()[0])
        except Exception:
            self.status("Select a valid camera index first.")
            return
        # parse resolution
        r = self.res_var.get()
        try:
            w,h = map(int, r.split("x"))
        except Exception:
            w,h = 640,480
        self._capture_size = (w,h)
        # open capture
        try:
            # prefer faster backend on Windows and set low-latency options
            if platform.system().lower().startswith("win"):
                try:
                    self.cap = cv2.VideoCapture(cam_idx, cv2.CAP_DSHOW)
                except Exception:
                    self.cap = cv2.VideoCapture(cam_idx)
            else:
                self.cap = cv2.VideoCapture(cam_idx)
            # request size
            self.cap.set(cv2.CAP_PROP_FRAME_WIDTH, w)
            self.cap.set(cv2.CAP_PROP_FRAME_HEIGHT, h)
            # try MJPG for faster transfers on UVC cams
            try:
                fourcc = cv2.VideoWriter_fourcc(*"MJPG")
                self.cap.set(cv2.CAP_PROP_FOURCC, fourcc)
            except Exception:
                pass
            # reduce internal buffering where supported
            try:
                self.cap.set(cv2.CAP_PROP_BUFFERSIZE, 1)
            except Exception:
                pass
            # ask a reasonable FPS (driver may ignore)
            try:
                self.cap.set(cv2.CAP_PROP_FPS, 30)
            except Exception:
                pass
            time.sleep(0.1)
            if not self.cap.isOpened():
                self.status("Failed to open camera.")
                self.log("Failed to open camera (isOpened returned False).")
                try:
                    self.cap.release()
                except Exception:
                    pass
                self.cap = None
                return
        except Exception:
            self.status("Camera open error."); self.log("Camera open error.")
            self.cap = None
            return
        self.camera_index = cam_idx
        # start reader thread
        self._reader_running = True
        self.reader_thread = threading.Thread(target=self._reader_loop, daemon=True)
        self.reader_thread.start()
        # open video window
        self._open_video_window()
        # check whether the camera supports autofocus and focus properties
        self._focus_supported = False
        try:
            # try to read current autofocus and focus properties
            af = self.cap.get(cv2.CAP_PROP_AUTOFOCUS)
            f = self.cap.get(cv2.CAP_PROP_FOCUS)
            # some backends return -1 or 0 for unsupported; treat numeric returns as support
            if af is not None and af != -1:
                self._focus_supported = True
        except Exception:
            self._focus_supported = False
        # enable or disable focus UI accordingly
        if self._focus_supported:
            self.af_cb.config(state="normal")
            self.focus_s.config(state="disabled" if self.auto_focus_var.get() else "normal")
            # apply initial autofocus or focus value
            try:
                self.cap.set(cv2.CAP_PROP_AUTOFOCUS, 1 if self.auto_focus_var.get() else 0)
                if not self.auto_focus_var.get():
                    self.cap.set(cv2.CAP_PROP_FOCUS, int(self.focus_value))
            except Exception:
                pass
        self.open_btn.config(text="Close")
        self.status(f"Camera {cam_idx} opened at {w}x{h}")
        # remember selected camera/res + UID
        try:
            self._pending_select_cam_idx = int(cam_idx)
            self._pending_select_res = f"{w}x{h}"
            # capture UID from current display selection
            sel_disp = self.cam_var.get()
            self._current_camera_uid = self._camera_uid_map.get(sel_disp)
            self._pending_select_cam_uid = self._current_camera_uid
        except Exception:
            pass
        # apply per-camera adjustments now that camera is open
        self._apply_camera_profile_to_ui(self._current_camera_key())
        self._save_settings()

    def _close_camera(self):
        self._reader_running = False
        if self.reader_thread:
            self.reader_thread.join(timeout=0.5)
            self.reader_thread = None
        if self.cap:
            try:
                self.cap.release()
            except Exception:
                pass
            self.cap = None
        self.camera_index = None
        self.open_btn.config(text="Open")
        self.status("Camera closed.")
        self._save_settings()
        # close video window if exists
        if self.video_win:
            try:
                self.video_win.destroy()
            except Exception:
                pass
            self.video_win = None
            self.video_label = None

    def _reader_loop(self):
        # background frame reader: updates self._latest_frame
        while self._reader_running and self.cap:
            try:
                # read latest frame; drop if UI is busy or update interval not reached
                ret, frame = self.cap.read()
                if not ret:
                    time.sleep(0.005)
                    continue
                with self._frame_lock:
                    self._latest_frame = frame
                # fps update
                self._frame_counter += 1
                now = time.time()
                if now - self._fps_last_time >= 1.0:
                    self._current_fps = self._frame_counter
                    self._frame_counter = 0
                    self._fps_last_time = now
                # throttle UI scheduling (frame dropping)
                if (now - self._last_ui_time) * 1000.0 >= self._ui_interval_ms and not self._ui_busy:
                    self._last_ui_time = now
                    if self.video_win:
                        self.root.after(0, self._update_video_frame)
                else:
                    # lightly yield
                    time.sleep(0.001)
            except Exception:
                time.sleep(0.01)

    # ---------- video window ----------
    def _open_video_window(self):
        if self.video_win:
            return
        self.video_win = tk.Toplevel(self.root)
        self.video_win.title(f"Camera {self.camera_index}")
        self.video_win.configure(bg=PALETTE_BG)
        self.video_win.geometry("800x600")
        # ensure closing the video window closes the camera and cleans up
        self.video_win.protocol("WM_DELETE_WINDOW", self._on_video_window_close)
         # allow resizing
        self.video_win.rowconfigure(0, weight=1)
        self.video_win.columnconfigure(0, weight=1)
        self.video_label = tk.Label(self.video_win, bg="black")
        self.video_label.grid(row=0, column=0, sticky="nsew")
        # bind mouse events for drawing & interaction
        self.video_label.bind("<ButtonPress-1>", self._video_mouse_down)
        self.video_label.bind("<B1-Motion>", self._video_mouse_move)
        self.video_label.bind("<ButtonRelease-1>", self._video_mouse_up)
        self.video_label.bind("<Button-3>", self._video_right_click)
        # middle button drag for panning when zoomed
        self.video_label.bind("<ButtonPress-2>", self._pan_start_evt)
        self.video_label.bind("<B2-Motion>", self._pan_move_evt)
        # allow SHIFT + Left drag to pan as well
        self.video_label.bind("<Shift-ButtonPress-1>", self._pan_start_evt)
        self.video_label.bind("<Shift-B1-Motion>", self._pan_move_evt)
        # apply same icon to video window
        try:
            icon_file = os.path.join(getattr(self, "_asset_dir", getattr(self, "_base_dir", os.getcwd())), "webcam.ico")
            if os.path.isfile(icon_file):
                try:
                    self.video_win.iconbitmap(icon_file)
                except Exception:
                    try:
                        ico_img = Image.open(icon_file)
                        self.video_win.iconphoto(True, ImageTk.PhotoImage(ico_img))
                    except Exception:
                        pass
        except Exception:
            pass
        # start periodic update
        self._update_video_frame()

    def _update_video_frame(self):
        if not self.video_label or not self.cap:
            return
        self._ui_busy = True
        try:
            # get latest frame
            with self._frame_lock:
                frame = self._latest_frame.copy() if self._latest_frame is not None else None
            if frame is None:
                # show "no camera" image
                img = Image.new("RGB", (640,480), (20,20,20))
                draw = ImageDraw.Draw(img)
                draw.text((10,10), "Waiting for camera...", fill=(200,200,200))
                imgtk = ImageTk.PhotoImage(img)
                self.video_label.imgtk = imgtk
                self.video_label.configure(image=imgtk)
                return
            # apply transforms: brightness/contrast
            try:
                frame = self._apply_adjustments(frame)
            except Exception:
                pass
            try:
                frame = self._apply_picture_ops(frame)
            except Exception:
                pass
            # determine label size to fit
            lbl_w = self.video_label.winfo_width() or self.video_label.winfo_reqwidth()
            lbl_h = self.video_label.winfo_height() or self.video_label.winfo_reqheight()
            if lbl_w <=1 or lbl_h <=1:
                lbl_w, lbl_h = 640,480
            # compute scale to fit while preserving aspect
            src_h, src_w = frame.shape[:2]
            scale = min(lbl_w/src_w, lbl_h/src_h)
            disp_w = max(1, int(src_w*scale))
            disp_h = max(1, int(src_h*scale))
            self._display_size = (disp_w, disp_h)
            self._last_disp_size = (disp_w, disp_h)
            self._last_scale = scale
            # store the image origin inside the label (label centers image by default)
            ox = max(0, (lbl_w - disp_w) // 2)
            oy = max(0, (lbl_h - disp_h) // 2)
            self._last_img_origin = (ox, oy)
            # resize frame for display
            try:
                disp = cv2.resize(frame, (disp_w, disp_h), interpolation=cv2.INTER_AREA)
            except Exception:
                disp = frame
            # draw overlays and preview
            disp_bgr = disp.copy()
            self._draw_overlays_on_image(disp_bgr, display=True)
            # overlay status (zoom, focus, resolution, fps)
            try:
                import cv2 as _cv
                zoom_txt = f"Zoom: {self.zoom_factor.get():.1f}x"
                res_txt = f"Res: {self._capture_size[0]}x{self._capture_size[1]}"
                fps_txt = f"FPS: {self._current_fps}"
                overlay_lines = [zoom_txt, res_txt, fps_txt]
                yoff = 16
                for line in overlay_lines:
                    _cv.putText(disp_bgr, line, (8, yoff), _cv.FONT_HERSHEY_SIMPLEX, 0.5, (220,220,220), 1, _cv.LINE_AA)
                    yoff += 16
                # focus bar/marker (bottom-left)
                bar_w, bar_h = 140, 6
                bx, by = 8, disp_bgr.shape[0] - 12
                _cv.rectangle(disp_bgr, (bx, by - bar_h), (bx + bar_w, by), (180,180,180), 1)
                if self._focus_supported:
                    if self.auto_focus_var.get():
                        # show autofocus + current focus value if readable
                        focus_val = None
                        try:
                            fv = self.cap.get(cv2.CAP_PROP_FOCUS)
                            if fv not in (-1, None):
                                focus_val = int(fv)
                        except Exception:
                            focus_val = None
                        af_text = f"AF:{focus_val}" if focus_val is not None else "AF"
                        _cv.putText(disp_bgr, af_text, (bx + bar_w + 6, by),
                                    _cv.FONT_HERSHEY_SIMPLEX, 0.5, (220,220,220), 1, _cv.LINE_AA)
                    else:
                        t = max(0.0, min(1.0, self.focus_value / 255.0))
                        mx = int(bx + t * bar_w)
                        _cv.line(disp_bgr, (mx, by - bar_h - 3), (mx, by + 3), (0, 220, 0), 2)
            except Exception:
                pass
            # convert to PIL and show
            disp_rgb = cv2.cvtColor(disp_bgr, cv2.COLOR_BGR2RGB)
            img = Image.fromarray(disp_rgb)
            imgtk = ImageTk.PhotoImage(img)
            self.video_label.imgtk = imgtk
            self.video_label.configure(image=imgtk)
            # schedule next update (fallback)
            if self._reader_running:
                self.video_label.after(self._ui_interval_ms, lambda: None)
        finally:
            self._ui_busy = False

    # --- pan handlers (for zoomed image) ---
    def _pan_start_evt(self, event):
        if self.zoom_factor.get() <= 1.0:
            return
        self._pan_start = (event.x, event.y)

    def _pan_move_evt(self, event):
        if self.zoom_factor.get() <= 1.0 or self._pan_start is None:
            return
        dx = event.x - self._pan_start[0]
        dy = event.y - self._pan_start[1]
        self._pan_start = (event.x, event.y)
        # invert X direction while panning
        self.pan_offset[0] -= dx
        # invert Y direction only while moving picture in zoom mode
        self.pan_offset[1] -= dy
        # clamp panning to image content
        with self._frame_lock:
            frame = self._latest_frame
        if frame is not None:
            h, w = frame.shape[:2]
            z = max(1.0, self.zoom_factor.get())
            cw = int(w / z)
            ch = int(h / z)
            max_x = (w - cw) // 2
            max_y = (h - ch) // 2
            self.pan_offset[0] = max(-max_x, min(max_x, self.pan_offset[0]))
            self.pan_offset[1] = max(-max_y, min(max_y, self.pan_offset[1]))
        self._update_video_frame()

    # ---------- overlay drawing / interaction ----------
    def _video_mouse_down(self, event):
        mode = self.mode_var.get()
        x,y = event.x, event.y
        # ignore when SHIFT is down (used for panning)
        if (event.state & 0x0001):  # Shift mask
            return
        if mode == "none":
            # try select overlay
            idx = self._hit_test_overlay((x,y))
            if idx is not None:
                self.selected_overlay = idx
                self._moving = True
                self._move_last = (x,y)
                self.status("Selected overlay %d" % idx)
            else:
                self.selected_overlay = None
            return
        # start drawing new overlay — store in normalized display coordinates
        self._draw_start = self._to_norm((x,y))
        self._current_preview = (mode, self._draw_start, self._draw_start, self.swatch_color)

    def _video_mouse_move(self, event):
        if self._moving and self.selected_overlay is not None:
            x,y = event.x,event.y
            dx = x - self._move_last[0]; dy = y - self._move_last[1]
            # move selected overlay in normalized space
            disp_w, disp_h = self._last_disp_size
            ddx = (dx / float(max(1,disp_w)))
            ddy = (dy / float(max(1,disp_h)))
            mode, p1, p2, color = self.overlays[self.selected_overlay]
            new_p1 = (p1[0]+ddx, p1[1]+ddy)
            new_p2 = (p2[0]+ddx, p2[1]+ddy)
            self.overlays[self.selected_overlay] = (mode, new_p1, new_p2, color)
            self._move_last = (x,y)
            self._update_video_frame()
            return
        if not getattr(self, "_draw_start", None):
            return
        x,y = event.x,event.y
        self._current_preview = (self.mode_var.get(), self._draw_start, self._to_norm((x,y)), self.swatch_color)
        self._update_video_frame()

    def _video_mouse_up(self, event):
        if self._moving:
            self._moving = False
            self._move_last = (0,0)
            return
        if not getattr(self, "_draw_start", None):
            return
        x,y = event.x,event.y
        mode = self.mode_var.get()
        new = (mode, self._draw_start, self._to_norm((x,y)), self.swatch_color)
        self.overlays.append(new)
        self._current_preview = None
        self._draw_start = None
        self.status(f"Added {mode}")
        # auto-return to none after drawing
        self.mode_var.set("none")
        self._update_video_frame()

    # --- overlay context menu and actions ---
    def _video_right_click(self, event):
        idx = self._hit_test_overlay((event.x, event.y))
        if idx is None:
            return
        self.selected_overlay = idx
        menu = tk.Menu(self.video_win, tearoff=0)
        menu.add_command(label="Delete", command=self._delete_selected_overlay)
        menu.add_command(label="Recolor", command=self._recolor_selected_overlay)
        menu.add_command(label="Bring to Front", command=self._bring_front)
        menu.add_command(label="Send to Back", command=self._send_back)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _delete_selected_overlay(self):
        if self.selected_overlay is not None:
            try:
                self.overlays.pop(self.selected_overlay)
            except Exception:
                pass
            self.selected_overlay = None
            self._update_video_frame()

    def _recolor_selected_overlay(self):
        if self.selected_overlay is None:
            return
        init = self._colhex(self.overlays[self.selected_overlay][3])
        res = colorchooser.askcolor(color=init, parent=self.video_win)
        if res and res[0]:
            rgb = tuple(int(c) for c in res[0])
            mode, p1n, p2n, _ = self.overlays[self.selected_overlay]
            self.overlays[self.selected_overlay] = (mode, p1n, p2n, rgb)
            self._update_video_frame()

    def _bring_front(self):
        if self.selected_overlay is None:
            return
        item = self.overlays.pop(self.selected_overlay)
        self.overlays.append(item)
        self.selected_overlay = len(self.overlays) - 1
        self._update_video_frame()

    def _send_back(self):
        if self.selected_overlay is None:
            return
        item = self.overlays.pop(self.selected_overlay)
        self.overlays.insert(0, item)
        self.selected_overlay = None
        self._update_video_frame()

    def _clear_overlays(self):
        self.overlays.clear()
        self.selected_overlay = None
        self._update_video_frame()

    def _to_norm(self, pt: Tuple[int,int]) -> Tuple[float,float]:
        # convert display pixel coords -> normalized (0..1) in current display
        disp_w, disp_h = self._last_disp_size
        ox, oy = self._last_img_origin
        # map label coords to image coords by removing centered origin
        px = pt[0] - ox
        py = pt[1] - oy
        # clamp to image bounds to avoid negatives during normalization
        px = max(0, min(disp_w, px))
        py = max(0, min(disp_h, py))
        x = max(0.0, min(1.0, (px / float(max(1, disp_w)))))
        y = max(0.0, min(1.0, (py / float(max(1, disp_h)))))
        return (x,y)

    def _from_norm(self, pt: Tuple[float,float]) -> Tuple[int,int]:
        # convert normalized -> display pixel coords for current display
        disp_w, disp_h = self._last_disp_size
        # Note: return image-space coords (no origin). Used for drawing into the image buffer.
        return (int(pt[0] * disp_w), int(pt[1] * disp_h))

    def _hit_test_overlay(self, pt: Tuple[int,int]) -> Optional[int]:
        # convert label coords to image-space coords for hit testing
        x,y = pt
        ox, oy = self._last_img_origin
        x -= ox; y -= oy
        # quickly reject if outside image area
        disp_w, disp_h = self._last_disp_size
        if x < 0 or y < 0 or x > disp_w or y > disp_h:
            return None
        for idx in range(len(self.overlays)-1, -1, -1):
            mode, p1n, p2n, _ = self.overlays[idx]
            x1,y1 = self._from_norm(p1n)
            x2,y2 = self._from_norm(p2n)
            if mode == "rect":
                # expanded grab margin
                margin = 8
                if (min(x1,x2)-margin) <= x <= (max(x1,x2)+margin) and (min(y1,y2)-margin) <= y <= (max(y1,y2)+margin):
                    return idx
            elif mode == "arrow":
                # bounding box hit
                bx1,bx2 = min(x1,x2), max(x1,x2)
                by1,by2 = min(y1,y2), max(y1,y2)
                margin = 8
                if bx1-margin <= x <= bx2+margin and by1-margin <= y <= by2+margin:
                    return idx
        return None

    def _draw_overlays_on_image(self, img_bgr, display=False):
        # img_bgr is numpy array in BGR at display size if display=True
        try:
            import cv2 as _cv
        except Exception:
            return
        targets = list(self.overlays)
        if getattr(self, "_current_preview", None):
            targets.append(self._current_preview)
        for mode,p1n,p2n,color in targets:
            x1,y1 = self._from_norm(p1n)
            x2,y2 = self._from_norm(p2n)
            bgr = (int(color[2]), int(color[1]), int(color[0]))
            thickness = 2
            if mode == "arrow":
                _cv.arrowedLine(img_bgr, (x1,y1), (x2,y2), bgr, thickness, tipLength=0.15)
            elif mode == "rect":
                _cv.rectangle(img_bgr, (x1,y1), (x2,y2), bgr, thickness)

    def _snapshot(self):
        if not self.cap:
            self.status("No camera open.")
            return
        # grab last frame
        with self._frame_lock:
            frame = self._latest_frame.copy() if self._latest_frame is not None else None
        if frame is None:
            self.status("No frame available for snapshot.")
            return
        # apply transforms before drawing overlays
        frame = self._apply_adjustments(frame)
        frame = self._apply_picture_ops(frame)
        cap_h, cap_w = frame.shape[:2]
        out = frame.copy()
        import cv2 as _cv
        for mode,p1n,p2n,color in self.overlays:
            # map normalized directly to current frame (already zoomed/rotated/mirrored) size
            x1 = int(p1n[0] * cap_w); y1 = int(p1n[1] * cap_h)
            x2 = int(p2n[0] * cap_w); y2 = int(p2n[1] * cap_h)
            bgr = (int(color[2]), int(color[1]), int(color[0]))
            if mode == "arrow":
                _cv.arrowedLine(out, (x1,y1),(x2,y2), bgr, 3, tipLength=0.15)
            elif mode == "rect":
                _cv.rectangle(out, (x1,y1),(x2,y2), bgr, 3)
        # save
        ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        fn = os.path.join(self.snapshot_dir, f"snapshot_{ts}.jpg")
        try:
            _cv.imwrite(fn, out)
            self.status(f"Snapshot saved: {fn}")
        except Exception:
            self.status("Failed to save snapshot.")
        # attempt to restore autofocus state (safe no-op on unsupported cams)
        try:
            if self._focus_supported:
                self.cap.set(cv2.CAP_PROP_AUTOFOCUS, 1 if self.auto_focus_var.get() else 0)
        except Exception:
            pass

    def _open_snapshot_folder(self):
        try:
            if platform.system().lower().startswith("win"):
                subprocess.Popen(["explorer", self.snapshot_dir])
            elif platform.system().lower().startswith("darwin"):
                subprocess.Popen(["open", self.snapshot_dir])
            else:
                subprocess.Popen(["xdg-open", self.snapshot_dir])
        except Exception:
            self.status("Cannot open folder.")

    # ---------- utilities ----------
    def _apply_adjustments(self, frame):
        # brightness & contrast: alpha=contrast, beta=brightness
        try:
            alpha = float(self.contrast)
            beta = float(self.brightness)
            frame = cv2.convertScaleAbs(frame, alpha=alpha, beta=beta)
        except Exception:
            pass
        return frame
    def _apply_picture_ops(self, frame):
        # rotate -> mirror -> zoom+pan; update crop info for mapping if needed
        deg = self.rotate_deg.get()
        if deg == 90:
            frame = cv2.rotate(frame, cv2.ROTATE_90_CLOCKWISE)
        elif deg == 180:
            frame = cv2.rotate(frame, cv2.ROTATE_180)
        elif deg == 270:
            frame = cv2.rotate(frame, cv2.ROTATE_90_COUNTERCLOCKWISE)
        if self.mirror.get():
            frame = cv2.flip(frame, 1)
        z = self.zoom_factor.get()
        if z > 1.01:
            h, w = frame.shape[:2]
            cw = max(1, int(w / z))
            ch = max(1, int(h / z))
            cx = w // 2 + int(self.pan_offset[0])
            cy = h // 2 + int(self.pan_offset[1])
            cx = max(cw//2, min(w - cw//2, cx))
            cy = max(ch//2, min(h - ch//2, cy))
            x1 = cx - cw//2
            y1 = cy - ch//2
            crop = frame[y1:y1+ch, x1:x1+cw]
            try:
                frame = cv2.resize(crop, (w, h), interpolation=cv2.INTER_LINEAR)
            except Exception:
                frame = crop
        return frame

    def _colhex(self, c: Tuple[int,int,int]) -> str:
        return "#{:02x}{:02x}{:02x}".format(*c)

    def status(self, text: str):
        self.status_lbl.config(text=text)

    def _get_system_camera_names(self) -> List[str]:
        """Best-effort camera name enumeration:
        - Windows: use WMIC or PowerShell to list PnP devices of class Camera/Image.
        - Linux: try v4l2-ctl --list-devices (if available).
        Returns a list of names (may be empty or length != number of indices)."""
        names: List[str] = []
        try:
            pf = platform.system().lower()
            if pf.startswith("win"):
                # try WMIC (available on older Windows) then PowerShell fallback
                try:
                    out = subprocess.check_output(["wmic", "path", "Win32_PnPEntity", "where", "PNPClass='Camera'", "get", "Name"], stderr=subprocess.DEVNULL, timeout=2, universal_newlines=True)
                    for line in out.splitlines():
                        line = line.strip()
                        if line and "Name" not in line:
                            names.append(line)
                except Exception:
                    try:
                        ps = ["powershell", "-Command", "Get-PnpDevice -Class Camera | Select-Object -ExpandProperty FriendlyName"]
                        out = subprocess.check_output(ps, stderr=subprocess.DEVNULL, timeout=2, universal_newlines=True)
                        for line in out.splitlines():
                            line = line.strip()
                            if line:
                                names.append(line)
                    except Exception:
                        pass
            else:
                # linux/mac: try v4l2-ctl
                try:
                    out = subprocess.check_output(["v4l2-ctl", "--list-devices"], stderr=subprocess.DEVNULL, timeout=2, universal_newlines=True)
                    # parse blocks: device name lines followed by /dev/video*
                    for line in out.splitlines():
                        line = line.rstrip()
                        if line and not line.startswith("\t") and not line.startswith(" "):
                            names.append(line.strip())
                except Exception:
                    pass
        except Exception:
            pass
        return names

    def _get_system_camera_devices(self) -> Tuple[List[str], List[str]]:
        """Return (indices_list, names_list) using system tools.
        - Linux: parse `v4l2-ctl --list-devices` to find /dev/videoN nodes -> indices.
        - Windows: use PowerShell Get-PnpDevice to get camera names and assume indices 0..n-1.
        Best-effort; returns ([],[]) on failure."""
        indices: List[str] = []
        names: List[str] = []
        try:
            pf = platform.system().lower()
            if pf.startswith("linux"):
                try:
                    out = subprocess.check_output(["v4l2-ctl", "--list-devices"], stderr=subprocess.DEVNULL, timeout=2, universal_newlines=True)
                    cur_name = None
                    for line in out.splitlines():
                        if line.strip() == "":
                            cur_name = None
                            continue
                        if not line.startswith("\t") and not line.startswith(" "):
                            cur_name = line.strip()
                            names.append(cur_name)
                        else:
                            # device path like \t/dev/video0
                            path = line.strip()
                            if path.startswith("/dev/video"):
                                try:
                                    idx = int(path.replace("/dev/video", "").split()[0])
                                    indices.append(str(idx))
                                except Exception:
                                    pass
                    # ensure names list length at least indices
                    # trim or pad names to match indices count
                    if len(names) < len(indices):
                        names = names + [""] * (len(indices) - len(names))
                    return indices, names
                except Exception:
                    return [], []
            elif pf.startswith("win"):
                # get friendly names via PowerShell
                try:
                    ps = ["powershell", "-Command", "Get-PnpDevice -Class Camera | Select-Object -ExpandProperty FriendlyName"]
                    out = subprocess.check_output(ps, stderr=subprocess.DEVNULL, timeout=2, universal_newlines=True)
                    for line in out.splitlines():
                        line = line.strip()
                        if line:
                            names.append(line)
                    # assume indices 0..n-1
                    indices = [str(i) for i in range(0, len(names))]
                    return indices, names
                except Exception:
                    return [], []
        except Exception:
            return [], []
        return [], []

    # Windows 11 camera enumerator (fast, no device opens)
    def _enum_win_cameras(self) -> List[Tuple[str, str, bool]]:
        """Return list of (FriendlyName, InstanceId, isPresent) for Windows cameras via PowerShell."""
        cams: List[Tuple[str, str, bool]] = []
        try:
            ps = [
                "powershell", "-NoProfile", "-Command",
                "(Get-PnpDevice -Class Camera | Select-Object Status, FriendlyName, InstanceId) | ConvertTo-Json -Compress"
            ]
            out = subprocess.check_output(ps, stderr=subprocess.DEVNULL, timeout=2, universal_newlines=True)
            data = json.loads(out) if out else []
            if isinstance(data, dict):
                data = [data]
            for item in data or []:
                name = str(item.get("FriendlyName", "")).strip()
                status = str(item.get("Status", "")).strip().lower()
                inst = str(item.get("InstanceId", "")).strip()
                if name:
                    cams.append((name, inst, status == "ok"))
        except Exception:
            pass
        return cams

    def _scan_cameras_sync(self):
        """Quick synchronous scan to populate camera list at startup.
        Prefer OS enumeration; fall back to tiny probe (0..2)."""
        try:
            idxs, names = self._get_system_camera_devices()
        except Exception:
            idxs, names = [], []

        values = []
        self._cam_display_map = {}
        if idxs:
            for i, idx in enumerate(idxs):
                name = names[i] if i < len(names) else ""
                avail = self._is_index_available(int(idx))
                disp_state = "available" if avail else "unavailable"
                display = f"{idx} - {name} ({disp_state})" if name else f"{idx} ({disp_state})"
                values.append(display)
                self._cam_display_map[display] = int(idx)
        else:
            # fallback small probe range
            sys_names = self._get_system_camera_names()
            for i in range(0, 3):
                try:
                    if self._is_index_available(i):
                        name = sys_names[i] if i < len(sys_names) else ""
                        display = f"{i} - {name} (available)" if name else f"{i} (available)"
                        values.append(display)
                        self._cam_display_map[display] = int(i)
                except Exception:
                    pass

        # update UI synchronously on main thread
        try:
            self.cam_cb.configure(values=values)
            if values:
                self.cam_var.set(values[0])
            else:
                self.cam_var.set("None")
        except Exception:
            # if UI not ready, ignore; async scan will populate later
            pass

    def _is_index_available(self, idx: int) -> bool:
        """Quick, best-effort check whether the given camera index can be opened.
        Opens a short-lived VideoCapture and releases it. Returns True if the device handle opened."""
        try:
            cap = cv2.VideoCapture(int(idx))
            if not cap:
                return False
            opened = cap.isOpened()
            try:
                # try a single read/grab to increase confidence on some drivers
                if opened:
                    try:
                        ret, _ = cap.read()
                        # some backends report opened but read may fail; still treat opened as available
                    except Exception:
                        pass
                cap.release()
            except Exception:
                try:
                    cap.release()
                except Exception:
                    pass
            return bool(opened)
        except Exception:
            return False

    def _on_video_window_close(self):
        try:
            self._close_camera()
        except Exception:
            pass

    # --- settings persistence ---
    def _parse_selected_camera_index(self) -> Optional[int]:
        try:
            sel = self.cam_var.get()
            if sel in getattr(self, "_cam_display_map", {}):
                return int(self._cam_display_map[sel])
            # fallback parse leading integer
            return int(str(sel).split()[0])
        except Exception:
            return None

    def _load_settings(self):
        try:
            if os.path.isfile(self._settings_path):
                with open(self._settings_path, "r", encoding="utf-8") as f:
                    data = json.load(f)
            else:
                data = {}
        except Exception:
            data = {}
        # apply with defaults
        try:
            self._pending_select_cam_idx = int(data.get("camera_index")) if "camera_index" in data else None
        except Exception:
            self._pending_select_cam_idx = None
        self._pending_select_res = str(data.get("resolution")) if data.get("resolution") else None
        try:
            self.brightness = int(data.get("brightness", self.brightness))
        except Exception:
            pass
        try:
            self.contrast = float(data.get("contrast", self.contrast))
        except Exception:
            pass
        try:
            self.auto_focus_var.set(bool(data.get("autofocus", self.auto_focus_var.get())))
        except Exception:
            pass
        try:
            self.focus_value = int(data.get("focus_value", self.focus_value))
        except Exception:
            pass
        try:
            self.mirror.set(bool(data.get("mirror", self.mirror.get())))
        except Exception:
            pass
        try:
            self.rotate_deg.set(int(data.get("rotate", self.rotate_deg.get())))
        except Exception:
            pass
        try:
            self.zoom_factor.set(float(data.get("zoom", self.zoom_factor.get())))
        except Exception:
            pass
        try:
            self._pending_select_cam_uid = data.get("camera_uid")
        except Exception:
            self._pending_select_cam_uid = None
        try:
            self._known_resolutions = dict(data.get("known_resolutions", {}))
        except Exception:
            self._known_resolutions = {}
        try:
            self._last_scanned_cameras = list(data.get("cameras", []))
        except Exception:
            self._last_scanned_cameras = []
        try:
            self._camera_adjustments = dict(data.get("camera_adjustments", {}))
        except Exception:
            self._camera_adjustments = {}

    def _save_settings(self):
        try:
            cam_idx = self._parse_selected_camera_index()
            sel_disp = self.cam_var.get()
            cam_uid = self._camera_uid_map.get(sel_disp) or self._current_camera_uid
            payload = {
                "camera_index": cam_idx if cam_idx is not None else self._pending_select_cam_idx,
                "camera_uid": cam_uid if cam_uid else self._pending_select_cam_uid,
                "resolution": self.res_var.get(),
                "known_resolutions": self._known_resolutions,
                "cameras": self._last_scanned_cameras,
                "brightness": int(self.brightness),
                "contrast": float(self.contrast),
                "mirror": bool(self.mirror.get()),
                "rotate": int(self.rotate_deg.get()),
                "zoom": float(self.zoom_factor.get()),
                "autofocus": bool(self.auto_focus_var.get()),
                "focus_value": int(self.focus_value),
                "camera_adjustments": self._camera_adjustments,
            }
            with open(self._settings_path, "w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
        except Exception:
            pass

    # --- adjustments reset (missing implementation) ---
    def _reset_adjustments(self):
        self.brightness = 0
        self.contrast = 1.0
        self.mirror.set(False)
        self.rotate_deg.set(0)
        self.zoom_factor.set(1.0)
        self.pan_offset = [0, 0]
        try:
            self.bright_s.set(self.brightness)
            self.contrast_s.set(int(self.contrast * 100))
        except Exception:
            pass
        self._update_video_frame()
        self._save_camera_profile()
        self._save_settings()
        self.status("Adjustments reset.")

    # --- capability helper (manual focus support) ---
    def _supports_manual_focus(self, idx: int) -> bool:
        """Return True if camera index appears to support manual focus."""
        try:
            cap = cv2.VideoCapture(int(idx))
            if not cap or not cap.isOpened():
                return False
            val = cap.get(cv2.CAP_PROP_FOCUS)
            # Some backends: -1 or 0 => unsupported. Positive usually means supported.
            if val not in (-1, 0, None):
                try: cap.release()
                except Exception: pass
                return True
            # Fallback heuristic: try to set focus value; if succeeds treat as supported.
            ok = cap.set(cv2.CAP_PROP_FOCUS, 10)
            try: cap.release()
            except Exception: pass
            return bool(ok)
        except Exception:
            return False

    # --- per-camera adjustments helpers ---
    def _save_camera_profile(self):
        key = self._current_camera_key()
        if not key:
            return
        try:
            self._camera_adjustments[key] = {
                "brightness": int(self.brightness),
                "contrast": float(self.contrast),
                "mirror": bool(self.mirror.get()),
                "rotate": int(self.rotate_deg.get()),
                "zoom": float(self.zoom_factor.get()),
                "autofocus": bool(self.auto_focus_var.get()),
                "focus_value": int(self.focus_value),
            }
        except Exception:
            pass

    def _apply_camera_profile_to_ui(self, key: Optional[str]):
        if not key:
            return
        prof = self._camera_adjustments.get(key)
        if not prof:
            return
        try:
            # apply vars
            self.brightness = int(prof.get("brightness", self.brightness))
            self.contrast = float(prof.get("contrast", self.contrast))
            self.mirror.set(bool(prof.get("mirror", self.mirror.get())))
            self.rotate_deg.set(int(prof.get("rotate", self.rotate_deg.get())))
            self.zoom_factor.set(float(prof.get("zoom", self.zoom_factor.get())))
            self.auto_focus_var.set(bool(prof.get("autofocus", self.auto_focus_var.get())))
            self.focus_value = int(prof.get("focus_value", self.focus_value))
            # update controls
            try:
                self.bright_s.set(self.brightness)
                self.contrast_s.set(int(self.contrast * 100))
                self.focus_s.set(self.focus_value)
                self.focus_s.config(state="disabled" if self.auto_focus_var.get() else "normal")
            except Exception:
                pass
            # refresh display
            self._update_video_frame()
        except Exception:
            pass

    # --- spinner helpers ---
    def _spinner_start(self):
        try:
            self._busy_ops += 1
            if self._busy_ops == 1:
                # first busy op => show spinner
                self.spinner.pack(side="right", padx=6)
                self.spinner.start(12)
        except Exception:
            pass

    def _spinner_stop(self):
        try:
            self._busy_ops = max(0, self._busy_ops - 1)
            if self._busy_ops == 0:
                self.spinner.stop()
                self.spinner.pack_forget()
        except Exception:
            pass

    # --- logging helpers ---
    def log(self, msg: str):
        try:
            ts = datetime.datetime.now().strftime("%H:%M:%S")
            line = f"[{ts}] {msg}"
            self._logs.append(line)
            # update UI if visible
            if hasattr(self, "log_text") and self.log_panel.winfo_ismapped():
                self.log_text.insert("end", line + "\n")
                self.log_text.see("end")
        except Exception:
            pass

    def _toggle_logs(self):
        try:
            if self.log_panel.winfo_ismapped():
                self.log_panel.pack_forget()
                self.log_btn.config(text="Logs")
            else:
                # populate existing logs and show
                self.log_text.delete("1.0", "end")
                for line in self._logs[-500:]:
                    self.log_text.insert("end", line + "\n")
                self.log_text.see("end")
                self.log_panel.pack(fill="both", expand=False, side="bottom", padx=12, pady=(0,8))
                self.log_btn.config(text="Hide Logs")
        except Exception:
            pass

    # --- dynamic camera/resolution helpers (missing) ---
    def _current_camera_key(self) -> Optional[str]:
        """Return stable key (UID or idx:N) for currently selected camera."""
        sel_disp = self.cam_var.get()
        uid = self._camera_uid_map.get(sel_disp)
        if uid:
            return uid
        idx = self._parse_selected_camera_index()
        return f"idx:{idx}" if idx is not None else None

    def _apply_known_resolutions_to_ui(self):
        """Populate resolution combobox with previously probed values for selected camera."""
        key = self._current_camera_key()
        if key and key in self._known_resolutions and self._known_resolutions[key]:
            vals = self._known_resolutions[key]
            try:
                self.res_cb.configure(values=vals)
                if self._pending_select_res in vals:
                    self.res_var.set(self._pending_select_res)
                else:
                    self.res_var.set(vals[0])
            except Exception:
                pass
        else:
            try:
                self.res_cb.configure(values=[])
                self.res_var.set(f"{self._capture_size[0]}x{self._capture_size[1]}")
            except Exception:
                pass

    def _switch_camera_to_selected(self):
        """Reopen currently opened camera to the newly selected index with preferred resolution."""
        new_idx = self._parse_selected_camera_index()
        if new_idx is None:
            return
        # decide resolution
        sel_res = self.res_var.get()
        try:
            w, h = map(int, sel_res.split("x"))
        except Exception:
            key = self._current_camera_key()
            if key and key in self._known_resolutions and self._known_resolutions[key]:
                try:
                    w, h = map(int, self._known_resolutions[key][0].split("x"))
                except Exception:
                    w, h = self._capture_size
            else:
                w, h = self._capture_size
        self._reopen_camera_with(new_idx, w, h)

    def _reopen_camera_with(self, idx: int, w: int, h: int):
        """Internal: close current capture and open given index @ resolution."""
        # stop reader
        self._reader_running = False
        if self.reader_thread:
            try: self.reader_thread.join(timeout=0.4)
            except Exception: pass
            self.reader_thread = None
        # release old
        if self.cap:
            try: self.cap.release()
            except Exception: pass
            self.cap = None
        self.camera_index = None
        self._capture_size = (w, h)
        self.status(f"Switching to camera {idx} @ {w}x{h}...")
        try:
            # open new
            if platform.system().lower().startswith("win"):
                try:
                    self.cap = cv2.VideoCapture(idx, cv2.CAP_DSHOW)
                except Exception:
                    self.cap = cv2.VideoCapture(idx)
            else:
                self.cap = cv2.VideoCapture(idx)
            self.cap.set(cv2.CAP_PROP_FRAME_WIDTH, w)
            self.cap.set(cv2.CAP_PROP_FRAME_HEIGHT, h)
            try: self.cap.set(cv2.CAP_PROP_FOURCC, cv2.VideoWriter_fourcc(*"MJPG"))
            except Exception: pass
            try: self.cap.set(cv2.CAP_PROP_BUFFERSIZE, 1)
            except Exception: pass
            try: self.cap.set(cv2.CAP_PROP_FPS, 30)
            except Exception: pass
            time.sleep(0.08)
            if not self.cap or not self.cap.isOpened():
                self.status("Reopen failed.")
                self.log(f"Reopen failed for camera {idx}")
                return
            self.camera_index = idx
            # reader restart
            self._reader_running = True
            self.reader_thread = threading.Thread(target=self._reader_loop, daemon=True)
            self.reader_thread.start()
            if not self.video_win:
                self._open_video_window()
            # focus capability
            self._focus_supported = False
            try:
                af = self.cap.get(cv2.CAP_PROP_AUTOFOCUS)
                if af is not None and af != -1:
                    self._focus_supported = True
            except Exception:
                self._focus_supported = False
            if self._focus_supported:
                self.af_cb.config(state="normal")
                self.focus_s.config(state="disabled" if self.auto_focus_var.get() else "normal")
                try:
                    self.cap.set(cv2.CAP_PROP_AUTOFOCUS, 1 if self.auto_focus_var.get() else 0)
                    if not self.auto_focus_var.get():
                        self.cap.set(cv2.CAP_PROP_FOCUS, int(self.focus_value))
                except Exception:
                    pass
            self.open_btn.config(text="Close")
            self.status(f"Camera {idx} opened at {w}x{h}")
            # update pending selections
            self._pending_select_cam_idx = idx
            self._pending_select_res = f"{w}x{h}"
            sel_disp = self.cam_var.get()
            self._current_camera_uid = self._camera_uid_map.get(sel_disp)
            self._pending_select_cam_uid = self._current_camera_uid
            # apply camera profile
            self._apply_camera_profile_to_ui(self._current_camera_key())
        except Exception:
            self.status("Reopen error.")
            self.log("Reopen error (exception).")
        finally:
            self._save_settings()

def main():
    root = tk.Tk()
    app = USBCameraApp(root)
    root.mainloop()
    return 0

if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()  # for PyInstaller (Windows)
    raise SystemExit(main())
