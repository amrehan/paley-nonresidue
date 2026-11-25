#!/usr/bin/env python3
"""Bulk-check the riemann-hypothesis community cache after an interrupted download.

`lake exe cache get` stops at the FIRST missing/corrupt archive it meets, so a download that
dropped many connections (e.g. its 500-way parallel fetch through Docker Desktop's network
proxy) needs one retry per bad file. This helper uses the repo's own scripts to select the same
immutable, SHA-256-pinned module manifest that `cache get` restores from, hashes EVERY archive
in .lake/cache/artifacts against it, and deletes the ones that do not match, so a single
retry re-fetches all of them.

It only deletes cache files that fail the repo's own SHA-256 check; it never trusts or
installs anything itself. Usage: verify-rh-cache.py <riemann-hypothesis checkout>
"""
import hashlib, importlib.util, os, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

root = Path(sys.argv[1]).resolve()
spec = importlib.util.spec_from_file_location("rh_ci_cache_get", root / "scripts" / "ci-cache-get.py")
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)

identity = ci.current_identity(root)
record, cached = ci.find_record(root, identity), {}
if record is None:
    record, cached = ci.baseline_record(identity)
if record is None:
    sys.exit("no matching cache record for this checkout")
fetch = lambda key, maximum=ci.MAX_JSON: cached[key] if key in cached else ci.fetch(key, maximum)
_, rows = ci.validated_blobs(record, identity, fetch)

cache = Path(os.environ.get("LAKE_CACHE_DIR", str(root / ".lake/cache"))).resolve() / "artifacts"

def check(row):
    _, _, artifact, digest = row
    path = cache / artifact
    if not path.is_file():
        return "missing", path
    with open(path, "rb") as f:
        if hashlib.file_digest(f, "sha256").hexdigest() != digest:
            return "corrupt", path
    return None

with ThreadPoolExecutor(max_workers=8) as pool:
    bad = [r for r in pool.map(check, rows) if r]
corrupt = [p for kind, p in bad if kind == "corrupt"]
for p in corrupt:
    p.unlink()
print(f"checked {len(rows)} archives: {len(corrupt)} corrupt (deleted), "
      f"{len(bad) - len(corrupt)} missing")
sys.exit(1 if bad else 0)
