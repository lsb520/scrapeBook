@echo off
cd /d "%~dp0"
python -m pip show pyinstaller >nul 2>nul
if errorlevel 1 (
    echo PyInstaller is not installed. Installing now...
    python -m pip install pyinstaller
)

python -m PyInstaller --onefile --windowed --name NovelScraper --icon assets\app.ico --add-data "assets;assets" app.py

echo.
echo Build finished. The exe should be here:
echo %cd%\dist\NovelScraper.exe
pause
