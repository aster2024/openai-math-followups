import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))

"""Arithmetic-gate protocol fixture stopping after the first of two rounds (Section 3.2).

This wrapper uses the common arithmetic-gate tensor construction.
"""
import sys
import p11_tensor_check as protocol

protocol.CASES["middle_stop"] = (2, 4, 3, (3, 5))
sys.argv = [__file__, "middle_stop"]
protocol.main()

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
