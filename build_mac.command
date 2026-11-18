#!/bin/bash
# Build BOTH Mac apps on a Mac (needs Python from python.org, 3.12 or newer):
#   GNHS Numeracy Teacher.app  (locked to approved computers, has the PIN + dashboard)
#   GNHS Numeracy Student.app  (only joins the teacher; contains no teacher code)
cd "$(dirname "$0")"
PY=python3
for p in /Library/Frameworks/Python.framework/Versions/*/bin/python3; do [ -x "$p" ] && PY="$p"; done
echo "Using: $PY ($($PY --version))"
$PY -m pip install -r requirements.txt || exit 1
$PY update_allowlist.py || echo "(could not refresh the approved list; using the one already in the folder)"
rm -rf build dist
COMMON="--noconfirm --windowed --icon icon.icns --hidden-import logo_data --hidden-import app_core --hidden-import webview --hidden-import app_role"

echo 'ROLE = "teacher"' > app_role.py
$PY -m PyInstaller $COMMON --name "GNHS Numeracy Teacher" --osx-bundle-identifier ph.gnhs.numeracy.teacher \
  --workpath build/teacher --specpath build/teacher main_desktop.py \
  --hidden-import numeracy_server --hidden-import license_check --hidden-import bundled_allowlist || exit 1

echo 'ROLE = "student"' > app_role.py
$PY -m PyInstaller $COMMON --name "GNHS Numeracy Student" --osx-bundle-identifier ph.gnhs.numeracy.student \
  --workpath build/student --specpath build/student main_desktop.py \
  --exclude-module numeracy_server --exclude-module bundled_allowlist || exit 1

echo 'ROLE = "teacher"' > app_role.py      # leave the folder in its default state
echo
echo "Done. Both apps are in the dist folder: GNHS Numeracy Teacher.app and GNHS Numeracy Student.app"
open dist
