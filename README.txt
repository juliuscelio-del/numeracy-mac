GNHS NUMERACY DRILL - MAC  (TWO SEPARATE APPS)
==============================================
  GNHS Numeracy Teacher.app  - PIN + dashboard, runs the drill. Locked to computers Julius approved.
  GNHS Numeracy Student.app  - only joins the teacher's drill. No lock, and it contains no teacher code.
Each app shows only its own screen (there is no Teacher/Student button). Give students the Student app only.
Data is saved in Documents/GNHS-Numeracy-Data (teacher). Forgot the PIN? Delete gnhs-pin.json there.

BUILD ON YOUR MACBOOK
  1. Install Python 3.12+ from python.org (the Apple Python 3.9 gives a blank window).
  2. Terminal:
       cd <this folder>
       xattr -cr .
       bash build_mac.command
  3. Both apps are in dist. Drag them to Applications (or share the Student one with students).

(Or build on GitHub: upload this folder, open Actions. Artifacts: GNHS-Numeracy-Teacher-Mac,
 GNHS-Numeracy-Student-Mac, and the two Windows .exe files. Each release holds all four files and
 each app updates only itself.)

USE
  First open: right-click the app > Open > Open, or:  xattr -cr "/Applications/GNHS Numeracy Teacher.app"
  Same Wi-Fi as the students. Port 8000.

LICENSE (Teacher app only, same as GNHS Quiz)
  The Teacher app only runs on computers Julius approved. It uses the SAME signed list and the SAME
  machine ID as GNHS Quiz, so a computer already approved for Quiz works here with no extra step.
  - Not approved: the app shows the computer's ID (Copy ID button). Send it to Julius.
  - Approve / remove computers ONLY in the Quiz project (Manage-Teachers.command, then upload
    server/allowlist.json as usual). No change to this app is needed.
  - The app downloads the newest list at launch and every hour while the drill runs. A removed
    computer saves its data and closes. Offline: it keeps the last list it has.
  - The GitHub build also refreshes bundled_allowlist.py by itself (update_allowlist.py).
  - The private key is NOT in this project and must never be added.
  - The Student app has no lock and no teacher code, so it cannot run a drill by itself.

app_role.py says which app a build is ("teacher" or "student"); the build scripts write it for you.
