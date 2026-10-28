#!/usr/bin/env python3
"""Compile and run the finite checks serially, with relative command records."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
os.setpriority(os.PRIO_PROCESS, 0, 19)
resource.setrlimit(resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3))
RESULTS = ROOT / 'results'
if RESULTS.exists():
    shutil.rmtree(RESULTS)
RESULTS.mkdir()
PYTHON = ['python3', '-B', '-I']
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
rows = []

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
    ]
    for index, command in enumerate(compile_cmds + commands):
        check = index - len(compile_cmds) + 1
        name = f'run_{check:02}' if check > 0 else f'compile_{index + 1:02}'
        start = time.monotonic()
        try:
            result = subprocess.run(command, capture_output=True, text=True, timeout=900)
        except subprocess.TimeoutExpired:
            print('FAIL: child exceeded 900 seconds; command=' + str(command))
            sys.exit(1)
        log = RESULTS / (name + '.txt')
        log.write_text(result.stdout + result.stderr)
        row = {
            'command': command, 'returncode': result.returncode,
            'seconds': round(time.monotonic() - start, 4), 'log': log.name,
            'stdout_lines': len(result.stdout.splitlines()),
            'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
        }
        rows.append(row)
        (RESULTS / 'manifest.json').write_text(json.dumps(rows, indent=2) + '\n')
        if result.returncode or (check > 0 and row['stdout_lines'] != 1):
            print('FAIL: ' + name + '; see results/' + log.name)
            sys.exit(1)

scope = {
    'status': 'PASS', 'test_runs': len(commands), 'compilations': len(compile_cmds),
    'started_utc': started, 'nice': os.getpriority(os.PRIO_PROCESS, 0),
    'address_space_bytes': 8 * 1024**3, 'per_child_timeout_seconds': 900,
    'serial': True, 'native_threads_per_child': 1,
    'source_sha256': {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(ROOT.iterdir()) if p.suffix in ('.py', '.cpp')
    },
}
(RESULTS / 'suite.json').write_text(json.dumps(scope, indent=2) + '\n')
print(f'PASS: {len(commands)} serial finite checks; 2 compilations; nice=19; 8 GiB; manifest=results/manifest.json')
