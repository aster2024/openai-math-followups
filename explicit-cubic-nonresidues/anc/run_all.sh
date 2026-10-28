#!/bin/sh
# Runs every check script (nice -n 19, python3 -I) and writes <name>.out next to it.  Each script prints one line.
cd "$(dirname "$0")" || exit 1
for s in constants digamma lemma5 kummer_conductor small_cases main_term zetaF hecke_fe hecke_lines hecke_zeros; do
  start=$(date +%s)
  nice -n 19 python3 -I "$s.py" > "$s.out" 2>&1
  echo "$s: $(( $(date +%s) - start )) s"
done
cat ./*.out
