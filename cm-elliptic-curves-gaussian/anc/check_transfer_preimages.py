from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Finite local check of the exact bijections in the two Poisson
transformations and the initialization.

This checks combinatorial identities, not an analytic moment estimate.
"""
from collections import defaultdict
from itertools import product
from pathlib import Path
import json

second = defaultdict(int)
second_wrong_t_condition = defaultdict(int)
second_counts = defaultdict(int)
seen_preimages = defaultdict(list)

# c,t,g,w,d,e are squarefree prime valuations. h is an arbitrary
# frequency valuation, truncated only after restricting the target r.
for c,t,g,w,d,e,h in product(range(2), range(2), range(2), range(2),
                            range(2), range(2), range(3)):
    if d > c or e > g:
        continue
    if c*t or g*(c+t) or w*(g+c+t+h):
        continue
    R = t+g-e
    f = c+e+w
    r = d+e+h
    if r > 2:
        continue
    assert R in (0,1) and f in (0,1) and R*f == 0
    # Individual column scale, and Fourier argument, are target-only.
    assert c+t+g+w == R+f
    assert d+h+2*g+2*t-e == r+2*R
    sign = (-1)**(e+w)
    key = (R,f,r)
    second[key] += sign
    second_counts[key] += 1
    seen_preimages[key].append((c,t,g,w,d,e,h))
    if not (t and r):
        second_wrong_t_condition[key] += sign

second_rows = []
for R,f,r in product(range(2),range(2),range(3)):
    if R*f:
        continue
    key = (R,f,r)
    expected = (1+R) * int(f == 0 or r >= 1)
    assert second[key] == expected, (key,second[key],expected)
    # Independently reconstruct the whole raw preimage list.
    reconstructed = []
    for t in range(R+1):
        for c,e,w in product(range(2),repeat=3):
            if c+e+w != f or e > r or (w and r):
                continue
            for d in range(min(c,r)+1):
                g = e+R-t
                h = r-d-e
                if h < 0:
                    continue
                reconstructed.append((c,t,g,w,d,e,h))
    assert sorted(reconstructed) == sorted(seen_preimages[key]), key
    second_rows.append({"R":R,"f":f,"r":r,
                        "preimages":second_counts[key],"signed_sum":second[key]})

wrong = [{"target":[R,f,r],"correct":second[(R,f,r)],
          "with_extra_t_row_coprimality":second_wrong_t_condition[(R,f,r)]}
         for R,f,r in second if second[(R,f,r)] != second_wrong_t_condition[(R,f,r)]]
assert wrong, "The check must detect the unwanted extra coprimality."

initial = defaultdict(list)
for g,v,e,h in product(range(2),range(2),range(2),range(3)):
    if e > g or g*v or v*h:
        continue
    b,f,r = g-e,e+v,e+h
    if r > 2:
        continue
    assert b in (0,1) and f in (0,1) and b*f == 0
    assert g+v == b+f
    # he^5v^4 = r f^4, with exact valuation equality.
    assert h+5*e+4*v == r+4*f
    assert e+v == f
    initial[(b,f,r)].append((g,v,e,h))

for b,f,r in product(range(2),range(2),range(3)):
    if b*f:
        continue
    e = int(f == 1 and r >= 1)
    reconstructed = (b+e,f-e,e,r-e)
    assert initial[(b,f,r)] == [reconstructed], (b,f,r)

report = {
    "status":"PASS",
    "scope":"Exact local bijections and signs only; no analytic certification.",
    "second_target_states":len(second_rows),
    "initial_target_states":len(initial),
    "second_preimages_checked":sum(second_counts.values()),
    "second_signed_table":second_rows,
    "extra_t_row_condition_counterexamples":wrong,
}
(_RESULTS / 'transfer_preimages.json').write_text(
    json.dumps(report,ensure_ascii=False,indent=2)+"\n")
_quiet(json.dumps({k:v for k,v in report.items()
                  if k not in ("second_signed_table",)},ensure_ascii=False))

print('check_transfer_preimages.py: PASS (see results/; scope in README.md)')
