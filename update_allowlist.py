"""Refreshes bundled_allowlist.py (the approved-computers list that ships inside the app).

  python update_allowlist.py                 downloads the newest signed list from GitHub
  python update_allowlist.py path/to/allowlist.json    uses the file from the Quiz project (server/allowlist.json)

The list is only accepted if its signature is valid. The GitHub build runs this automatically
(and keeps the committed copy if the download fails), so you normally never need to run it.
"""
import sys, os, json
import license_check as lc

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "bundled_allowlist.py")


def main():
    if len(sys.argv) > 1:
        with open(sys.argv[1], "r", encoding="utf-8") as f:
            lst = json.load(f)
    else:
        from urllib.request import Request, urlopen
        with urlopen(Request(lc.ALLOWLIST_URL, headers={"User-Agent": "GNHS-Numeracy-Build"}), timeout=20, context=lc._ctx()) as r:
            lst = json.loads(r.read().decode("utf-8"))
    lst = lc._verified(lst)
    if not lst:
        print("x The list has an INVALID signature. Nothing was written.")
        return 1
    old = lc._read_bundled()
    if old and lc._issued_ts(old["issuedAt"]) > lc._issued_ts(lst["issuedAt"]):
        print("OK kept the bundled list (it is newer than the one given).")
        return 0
    clean = {"issuedAt": lst["issuedAt"], "machines": [{"id": m["id"]} for m in lst["machines"]], "sig": lst["sig"]}
    with open(OUT, "w", encoding="utf-8") as f:
        f.write('"""Signed list of approved computers (same list as GNHS Quiz). Made by update_allowlist.py - do not edit by hand."""\n')
        f.write("ALLOWLIST = " + json.dumps(clean, indent=2) + "\n")
    print("OK bundled_allowlist.py written: %d computer(s), issued %s" % (len(clean["machines"]), clean["issuedAt"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
