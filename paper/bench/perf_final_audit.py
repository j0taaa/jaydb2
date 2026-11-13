#!/usr/bin/env python3
"""Final read-only engine/baseline/CPU audit; caller holds the heavy lock.

Run after perf_final_report.py succeeds. Writes only the new audit receipt.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from paper.bench.frequency import observe

REV = '1ea6ddc'
BUILD = ROOT / '.build/paper-bench'
OUT = ROOT / 'paper/evidence'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def main():
    existing = git('ls-tree', '-r', '--name-only', REV, '--', 'paper/evidence/').decode().splitlines()
    original_hashes = {}
    for name in existing:
        expected = git('show', f'{REV}:{name}')
        assert (ROOT / name).read_bytes() == expected, f'existing evidence changed: {name}'
        original_hashes[name] = hashlib.sha256(expected).hexdigest()
    assert not git('diff', REV, '--', 'server', 'src', 'contract', 'proof', 'tools', 'native',
                   'library', 'paper/main.tex', 'paper/slides.tex', 'paper/bench/run.py',
                   'paper/bench/workloads.py', 'paper/bench/fixtures.py'), 'protected sources changed'
    cpu = observe()
    governors = [v for p, v in cpu['settings'].items() if p.endswith('/scaling_governor')]
    assert len(governors) == 16 and set(governors) == {'powersave'}
    assert cpu['settings']['/sys/devices/system/cpu/intel_pstate/no_turbo'] == '0'
    restorations = []
    folders = {Path(p) for log in BUILD.glob('perf-final-*.log')
               for p in re.findall(r'CPU settings restored and verified: (.+)/restored.json', log.read_text())}
    for folder in sorted(folders):
        original = json.loads((folder / 'original.json').read_text())
        applied = json.loads((folder / 'applied.json').read_text())
        restored = json.loads((folder / 'restored.json').read_text())
        assert applied['verified'] and restored['verified']
        assert original['settings'] == restored['settings']
        restorations.append(dict(folder=str(folder.relative_to(ROOT)), original=original, applied=applied, restored=restored))
    assert len(restorations) == 13, len(restorations)
    commands = []
    for command, filename, required in [
        ('make build', 'perf-final-build.log', 'Finished `release`'),
        ('make -C .build/perf-final-baseline build', 'perf-final-baseline-build.log', 'Finished `release`'),
        ('PATH="$PWD/.build/perf-final-venv/bin:$PATH" python3 -m pytest paper/test_evidence.py',
         'perf-final-pytest.log', '30 passed'),
        ('.build/perf-final-venv/bin/python -B paper/bench/perf_final_report.py',
         'perf-final-report.log', 'PASS: new E2/E3/E5')]:
        log = (BUILD / filename).read_text()
        assert required in log, (command, log[-2000:])
        commands.append(dict(command=command, common_shell='flock /tmp/jaydb2-experiments-heavy.lock bash -c; ulimit -s unlimited',
                             result='PASS', returncode=0, log=log,
                             log_sha256=hashlib.sha256(log.encode()).hexdigest()))
    invocations = []
    for path in sorted(OUT.glob('perf-final-*.json')):
        data = json.loads(path.read_text())
        if 'runner' not in data or 'completed_utc' not in data['runner']:
            continue
        prefix = 'baseline-' if 'baseline-' in path.name else ''
        engine_root = ROOT / '.build/perf-final-baseline' if prefix else ROOT
        assert hashlib.sha256((engine_root / 'target/release/jaydb2').read_bytes()).hexdigest() == data['metadata']['binary_sha256']
        filename = path.stem + '.log'
        log = (BUILD / filename).read_text()
        assert 'CPU settings restored and verified:' in log
        invocations.append(dict(file=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                                runner=data['runner'], metadata=data['metadata'], log_sha256=hashlib.sha256(log.encode()).hexdigest()))
    assert len(invocations) == 10, len(invocations)
    assert git('-C', '.build/perf-final-baseline', 'rev-parse', 'HEAD').decode().startswith('3f28eb7')
    assert not git('-C', '.build/perf-final-baseline', 'status', '--porcelain')
    receipt = dict(commands=commands, benchmark_invocations=invocations,
                   benchmark_shell='flock /tmp/jaydb2-experiments-heavy.lock bash -c: ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B SCRIPT ARGS',
                   baseline_evidence_byte_identical=True, protected_sources_unchanged=True,
                   original_evidence_sha256=original_hashes, clock_restorations=restorations,
                   cpu_final=cpu, full_release_suite='Not rerun: benchmark-only override in task brief',
                   runtime_estimate='Historical E2 samples+registrations 576 s; E3 timed+ordinary context 1336 s; with setup/readback and three baseline E5 sessions comfortably below three hours.')
    sys.path.insert(0, str(ROOT / '.build/paper-bench/python'))
    import psycopg
    receipt['psycopg_version'] = psycopg.__version__
    receipt['formatting_note'] = ('Initial git diff --cached --check flagged Matplotlib SVG trailing whitespace. '
                                  'The generator now strips line-end whitespace without changing geometry; final check rerun after staging.')
    historical = json.loads((OUT / 'comparison.json').read_text())
    rerun = json.loads((OUT / 'perf-final-baseline-comparison.json').read_text())
    receipt['historical_baseline_source_matches_rerun'] = (
        historical['metadata']['source_sha256'] == rerun['metadata']['source_sha256'])
    assert receipt['historical_baseline_source_matches_rerun']
    (OUT / 'perf-final-validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'PASS: {len(existing)} original evidence files byte-identical; protected sources unchanged; '
          f'{len(invocations)} E2/E3/E5 runs, 3 phase runs and 13 clock restorations; all CPUs powersave / no_turbo=0')


if __name__ == '__main__':
    main()
