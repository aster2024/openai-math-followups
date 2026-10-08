"""Rerun all exact certificates serially in this one Python process."""
from pathlib import Path
from datetime import datetime, timezone
import contextlib
import hashlib
import json
import runpy
import sys

root=Path(__file__).resolve().parent
sys.path.insert(0,str(root))
scripts=[
    "verify_rational.py","verify_quadratic.py","verify_cubic.py",
    "verify_structure.py","verify_phases.py",
]
rows=[]
for name in scripts:
    output=root/(name.removesuffix(".py")+".out.txt")
    with output.open("w") as stream,contextlib.redirect_stdout(stream):
        runpy.run_path(str(root/name),run_name="__main__")
    text=output.read_text()
    checks=sum(line.startswith("PASS ") for line in text.splitlines())
    rows.append({
        "script":name,"output":output.name,"checks":checks,
        "script_sha256":hashlib.sha256((root/name).read_bytes()).hexdigest(),
        "output_sha256":hashlib.sha256(output.read_bytes()).hexdigest(),
        "status":"PASS",
    })
    print(name,"PASS",checks,"checks")
receipt={
    "completed_utc":datetime.now(timezone.utc).isoformat(),
    "arithmetic":"Fraction; quadratic and cubic quotient fields; rational intervals",
    "execution":"one process; run with nice -n 19",
    "total_checks":sum(x["checks"] for x in rows),
    "library_sha256":hashlib.sha256((root/"exact.py").read_bytes()).hexdigest(),
    "results":rows,
}
(root/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print("TOTAL",receipt["total_checks"],"PASS")
