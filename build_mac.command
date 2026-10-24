#!/bin/bash
# Build the Mac app on a Mac (needs Python from python.org, 3.12 or newer).
cd "$(dirname "$0")"
PY=python3
for p in /Library/Frameworks/Python.framework/Versions/*/bin/python3; do [ -x "$p" ] && PY="$p"; done
echo "Using: $PY ($($PY --version))"
$PY -m pip install -r requirements.txt || exit 1
rm -rf build dist
$PY -m PyInstaller --noconfirm --windowed --name "GNHS Numeracy Drill" --icon icon.icns main_desktop.py \
  --hidden-import numeracy_server --hidden-import logo_data --hidden-import app_core --hidden-import webview || exit 1
echo
echo "Done. Your app is in the dist folder: GNHS Numeracy Drill.app"
open dist
