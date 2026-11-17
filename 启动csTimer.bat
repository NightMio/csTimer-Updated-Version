@echo off
chcp 65001 >nul
cd /d "%~dp0"
set "PS=C:\Windows\System32\WindowsPowerShell\v1.0\powershell.exe"
if not exist "%PS%" set "PS=powershell"
"%PS%" -NoProfile -ExecutionPolicy Bypass -File "%~dp0_serve.ps1" %*
if errorlevel 1 pause
