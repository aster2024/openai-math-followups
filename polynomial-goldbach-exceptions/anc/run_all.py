#!/usr/bin/env python3
"""Run the distributed checks serially; each invoked check prints one line."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def main():
    start = time.monotonic()
    commands = [[sys.executable, str(ROOT / "exact_checks.py")],
                [sys.executable, str(ROOT / "interface_checks.py")],
                [sys.executable, str(ROOT / "verify_claims.py")]]
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    (ROOT / "results").mkdir(parents=True, exist_ok=True)
    receipts = []
    for cmd in commands:
        result = subprocess.run(cmd, cwd=ROOT, env=env, text=True, capture_output=True, timeout=120)
        lines = result.stdout.strip().splitlines()
        if result.returncode or len(lines) != 1 or not lines[0].startswith("PASS "):
            raise RuntimeError({"command": [Path(v).name for v in cmd],
                                "returncode": result.returncode,
                                "stdout": result.stdout, "stderr": result.stderr})
        print(lines[0], flush=True)
        receipts.append({"command": [Path(v).name for v in cmd],
                         "returncode": result.returncode,
                         "summary": lines[0], "stderr": result.stderr})
    (ROOT / "results/run_all.json").write_text(json.dumps(
        {"status": "PASS", "serial": True, "checks": receipts,
         "elapsed_seconds": round(time.monotonic()-start, 3)}, indent=2)+"\n")
    print("PASS run_all: 3 checks completed serially")


if __name__ == "__main__":
    main()
