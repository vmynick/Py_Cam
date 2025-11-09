@echo off
setlocal
REM Build Py_Cam executable

REM Ensure virtual environment (optional)
REM call .venv\Scripts\activate

pip install --upgrade pyinstaller

REM Directory build (faster startup, easier debugging)
pyinstaller Py_Cam.py --name Py_Cam --noconsole --icon webcam.ico --add-data "webcam.ico;." --hidden-import cv2 --hidden-import PIL.Image --hidden-import PIL.ImageTk

REM Uncomment for single-file build (slower start):
REM pyinstaller Py_Cam.py --onefile --name Py_Cam --noconsole --icon webcam.ico --add-data "webcam.ico;." --hidden-import cv2 --hidden-import PIL.Image --hidden-import PIL.ImageTk

echo Build complete. See dist\Py_Cam\
pause
