#!/usr/bin/env python3
"""Run finite checks in bounded serial batches, optionally verifying completed rows."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
ap = argparse.ArgumentParser()
ap.add_argument('--part', required=True, choices=('baseline', 'layers', 'residues'))
ap.add_argument('--resume', action='store_true')
args = ap.parse_args()
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
os.setpriority(os.PRIO_PROCESS, 0, 19)
resource.setrlimit(resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3))
RESULTS = ROOT / 'results'
if args.part == 'baseline' and not args.resume and RESULTS.exists():
    shutil.rmtree(RESULTS)
RESULTS.mkdir(exist_ok=True)
(RESULTS / 'suite.json').unlink(missing_ok=True)
math_hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(ROOT.iterdir()) if p.suffix in ('.py', '.cpp') and p.name != 'run_all.py'}
hash_file = RESULTS / 'source_hashes.json'
if hash_file.exists() and json.loads(hash_file.read_text()) != math_hashes:
    sys.exit('FAIL: check sources changed; restart with --part baseline')
hash_file.write_text(json.dumps(math_hashes, indent=2) + '\n')
manifest = RESULTS / 'manifest.json'
rows = json.loads(manifest.read_text()) if manifest.exists() else []
PYTHON = ['python3', '-B', '-I']
normal = lambda command: [re.sub(r'\.check-bin-[^/]+', '<temporary>', arg) for arg in command]
executed = 0

with tempfile.TemporaryDirectory(prefix='.check-bin-', dir=ROOT) as temporary:
    binary_dir = Path(temporary).name
    compile_cmds = [
        ['g++', '-O2', '-std=c++17', name + '.cpp', '-o', binary_dir + '/' + name]
        for name in ('finite_audit', 'protocol_exact_check')
    ]
    commands = [
        ['./' + binary_dir + '/finite_audit', 'sign'],
        ['./' + binary_dir + '/finite_audit', 'marker'],
        ['./' + binary_dir + '/finite_audit', 'directed'],
        PYTHON + ['p6_sign_check.py', '1', '300'],
        PYTHON + ['p6_sign_check.py', '2', '300'],
        PYTHON + ['p6_blockcount_check.py'],
        PYTHON + ['p7_p8_filter_check.py', '3'],
        PYTHON + ['p7_p8_filter_check.py', '4'],
        PYTHON + ['e2e_hc_network.py'],
        PYTHON + ['hc_accounting.py'],
        PYTHON + ['c2_p2_p3_check.py'],
        PYTHON + ['check_gadgets.py'],
        ['./' + binary_dir + '/protocol_exact_check', '2'],
        PYTHON + ['check_contraction_engine.py'],
        PYTHON + ['tensor_realization_check.py'],
        PYTHON + ['tensor_realization_t3_check.py'],
        PYTHON + ['p11_tensor_check.py', 'one_round_bad_seed'],
        PYTHON + ['p11_tensor_check.py', 'initial_stop'],
        PYTHON + ['p11_tensor_check.py', 'two_rounds'],
        PYTHON + ['p11_middle_stop.py'],
        PYTHON + ['check_unused_inputs.py'],
        PYTHON + ['check_G1_tensor.py'],
        PYTHON + ['check_G3_tensor.py'],
        PYTHON + ['check_thresholds.py'],
        PYTHON + ['check_cnf_arithmetic.py', '--max-inputs', '7'],
        PYTHON + ['check_cnf_reference.py', 'gates'],
        PYTHON + ['check_cnf_reference.py', 'arithmetic', '--start', '0', '--stop', '12'],
        PYTHON + ['check_cnf_layers.py', '--n', '5'],
        PYTHON + ['check_cnf_reference.py', 'graphs', '--n', '6', '--start', '30000', '--stop', '30032'],
        PYTHON + ['check_cnf_witness.py', '--n', '4', '--range', '2'],
        PYTHON + ['check_cnf_witness.py', '--n', '4', '--range', '2', '--optimisation'],
        PYTHON + ['check_cnf_paths.py', '--n', '5', '--path'],
        PYTHON + ['check_cnf_paths.py', '--n', '4', '--directed', '--start', '2048', '--stop', '2560', '--max-edges', '8'],
        PYTHON + ['check_cnf_paths.py', '--n', '4', '--directed', '--path', '--start', '3584', '--stop', '4096', '--max-edges', '8'],
        PYTHON + ['check_cnf_objects.py', '--n', '4'],
        PYTHON + ['check_cnf_weighted_objects.py', '--mode', 'steiner', '--stop', '4', '--progress', 'results/cnf_steiner.progress.jsonl'],
        PYTHON + ['check_cnf_weighted_objects.py', '--mode', 'cover', '--stop', '4', '--progress', 'results/cnf_cover.progress.jsonl'],
        PYTHON + ['check_cnf_weighted_objects.py', '--mode', 'dominating', '--stop', '4', '--progress', 'results/cnf_dominating.progress.jsonl'],
        PYTHON + ['check_cnf_weighted_objects.py', '--mode', 'fvs', '--stop', '4', '--progress', 'results/cnf_fvs.progress.jsonl'],
        PYTHON + ['check_cnf_failures.py'],
        PYTHON + ['check_cnf_steiner.py', '--start', '0', '--stop', '512', '--progress', 'results/cnf_steiner_low.progress.jsonl'],
        PYTHON + ['check_cnf_steiner.py', '--start', '3584', '--stop', '4096', '--progress', 'results/cnf_steiner_high.progress.jsonl'],
        PYTHON + ['check_cnf_modular.py', '--case', 'k6', '--bits', '2', '--stop', '20000', '--progress', 'results/cnf_modular.progress.jsonl'],
        PYTHON + ['check_cnf_boundaries.py', '--start-case', '2', '--stop-case', '8', '--skip-family'],
        PYTHON + ['check_cnf_large.py', '--p', '253'],
        PYTHON + ['check_cnf_large.py', '--p', '254'],
        PYTHON + ['check_cnf_scaling.py', '--max-power', '12'],
    ]
    plan = compile_cmds + commands
    selected = {'baseline': range(0, 26), 'layers': range(26, 44), 'residues': range(44, 49)}[args.part]
    rows += [None] * (len(plan) - len(rows))
    for index in selected:
        command = plan[index]
        check = index - len(compile_cmds) + 1
        name = f'run_{check:02}' if check > 0 else f'compile_{index + 1:02}'
        old = rows[index]
        if args.resume and old and normal(old['command']) == normal(command):
            log = RESULTS / old['log']
            if old['returncode'] == 0 and log.exists() and hashlib.sha256(log.read_bytes()).hexdigest() == old['log_sha256'] and (check <= 0 or old['stdout_lines'] == 1):
                continue
        start = time.monotonic()
        try:
            result = subprocess.run(command, capture_output=True, text=True, timeout=900)
        except subprocess.TimeoutExpired:
            sys.exit('FAIL: child exceeded 900 seconds; command=' + str(command))
        log = RESULTS / (name + '.txt')
        log.write_text(result.stdout + result.stderr)
        rows[index] = {'command': command, 'returncode': result.returncode,
                       'seconds': round(time.monotonic() - start, 4), 'log': log.name,
                       'stdout_lines': len(result.stdout.splitlines()),
                       'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
        manifest.write_text(json.dumps(rows, indent=2) + '\n')
        executed += 1
        if result.returncode or (check > 0 and rows[index]['stdout_lines'] != 1):
            sys.exit('FAIL: ' + name + '; see results/' + log.name)
    complete = all(row and row['returncode'] == 0 and normal(row['command']) == normal(plan[index])
                   and (index < 2 or row['stdout_lines'] == 1)
                   and hashlib.sha256((RESULTS / row['log']).read_bytes()).hexdigest() == row['log_sha256']
                   for index, row in enumerate(rows))
if complete:
    scope = {'status': 'PASS', 'test_runs': len(commands), 'compilations': len(compile_cmds),
             'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'nice': os.getpriority(os.PRIO_PROCESS, 0), 'address_space_bytes': 8 * 1024**3,
             'per_child_timeout_seconds': 900, 'serial': True, 'native_threads_per_child': 1,
             'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(ROOT.iterdir()) if p.suffix in ('.py', '.cpp')}}
    (RESULTS / 'suite.json').write_text(json.dumps(scope, indent=2) + '\n')
print(f'PASS: part={args.part}; executed={executed}; complete={complete}; checks={len(commands)}; manifest=results/manifest.json')
