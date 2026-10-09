#!/usr/bin/env python3
"""Compile the formalization against a built copy of the OpenAI library.

Usage:
    python3 build.py --oai /path/to/openai-math/lean [--lean /path/to/bin/lean]
                     [--jobs 3] [--out _build] [--target VerificationExplicit]

`--oai` is the Lake project directory of github.com/openai/math (its `lean/`
directory) at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, in which the
modules listed in `oai_imports.txt` have been built with `lake build`.
The script compiles every module in the import closure of the target in
dependency order with `lean -o`, stops at the first failure, and prints the
`#print axioms` lines of the target.
"""
import argparse, os, re, subprocess, sys, threading, time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--oai', required=True)
parser.add_argument('--lean', default='lean')
parser.add_argument('--jobs', type=int, default=3)
parser.add_argument('--out', default='_build')
parser.add_argument('--target', default='VerificationExplicit',
                    help='VerificationExplicit (Theorem 1.1 with the exponent 10^-200) or Verification')
parser.add_argument('--threads', default='2', help='LEAN_NUM_THREADS for each process')
args = parser.parse_args()

SRC = Path(__file__).resolve().parent
OUT = Path(args.out).resolve()
LOGS = OUT / 'logs'
LOGS.mkdir(parents=True, exist_ok=True)
OAI = Path(args.oai).resolve()

modules = {}
for path in SRC.rglob('*.lean'):
    if OUT in path.parents:
        continue
    modules['.'.join(path.relative_to(SRC).with_suffix('').parts)] = path
deps = {name: [d for d in re.findall(r'^import\s+([\w.]+)', path.read_text(), re.M) if d in modules]
        for name, path in modules.items()}
if args.target not in modules:
    sys.exit('unknown target ' + args.target)
need = set()
def visit(name):
    if name not in need:
        need.add(name)
        for d in deps[name]:
            visit(d)
visit(args.target)

search = [OUT / 'lib', OAI / '.lake/build/lib/lean']
packages = OAI / '.lake/packages'
if packages.is_dir():
    search += [p / '.lake/build/lib/lean' for p in sorted(packages.iterdir())
               if (p / '.lake/build/lib/lean').is_dir()]
env = dict(os.environ, LEAN_PATH=':'.join(map(str, search)), LEAN_NUM_THREADS=args.threads)

done, started, failed, lock = set(), set(), [], threading.Lock()

def compile_module(name):
    out = (OUT / 'lib').joinpath(*name.split('.')).with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(LOGS / (name + '.log'), 'w') as log:
        return subprocess.run([args.lean, '-DautoImplicit=false', '--root=' + str(SRC),
                               '-o', str(out), str(modules[name])],
                              env=env, stdout=log, stderr=subprocess.STDOUT).returncode

def worker():
    while True:
        with lock:
            if failed or len(done) == len(need):
                return
            ready = sorted(m for m in need if m not in started and all(d in done for d in deps[m]))
            name = ready[0] if ready else None
            if name:
                started.add(name)
        if name is None:
            time.sleep(0.2)
            continue
        code = compile_module(name)
        with lock:
            if code:
                failed.append(name)
            else:
                done.add(name)
            print(f'[{len(done)}/{len(need)}] {name}: {"ok" if code == 0 else "FAILED"}', flush=True)

start = time.time()
threads = [threading.Thread(target=worker) for _ in range(max(1, args.jobs))]
for t in threads: t.start()
for t in threads: t.join()
if failed:
    sys.exit(f'FAILED: {failed[0]} (see {LOGS / (failed[0] + ".log")})')
print(f'ALL PASS: {len(done)} modules in {round(time.time() - start)} s')
log = (LOGS / (args.target + '.log')).read_text().splitlines()
for i, line in enumerate(log):
    if 'depends on axioms' in line:
        print(line)
        j = i + 1
        while j < len(log) and not log[j].startswith("'") and log[j].strip().endswith((',', ']')):
            print(log[j]); j += 1
