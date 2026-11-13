#!/usr/bin/env python3
"""Run the unchanged E2/E3/E5 harness into a new, explicitly named evidence file.

Caller holds the common heavy lock and fixed-clock.sh. --root selects an
independently built Git checkout; no timing loops or workload flags are changed.
E5's original one-session experiment is repeated in separate invocations.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('experiment', choices=('prepared', 'comparison', 'scaling'))
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root, output = args.root.resolve(), args.output.resolve()
    if output.exists():
        parser.error(f'refusing to replace existing evidence: {output}')
    if os.environ.get('JAYDB_BENCH_RESUME'):
        parser.error('resume of historical evidence is forbidden')
    sys.path.insert(0, str(root))
    from paper.bench import run
    assert run.ROOT == root, (run.ROOT, root)
    run.BUILD.mkdir(parents=True, exist_ok=True)
    (run.BUILD / 'tmp').mkdir(exist_ok=True)
    started = time.time()
    runner = dict(
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        command=sys.argv, root=str(root), output=str(output),
        adaptation='Output redirection only; original experiment function unchanged.',
        harness_sha256={name: hashlib.sha256((root / 'paper/bench' / name).read_bytes()).hexdigest()
                        for name in ('run.py', 'workloads.py', 'fixtures.py')},
        started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(started)))

    def save(name, data):
        assert name == args.experiment + '.json', name
        data['runner'] = dict(runner, elapsed_wall_seconds=time.time() - started)
        tmp = output.with_suffix(output.suffix + '.tmp')
        tmp.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n')
        tmp.replace(output)

    run.save = save
    if args.experiment == 'prepared':
        run.prepared()
    else:
        from paper.bench import workloads
        getattr(workloads, args.experiment)()
    data = json.loads(output.read_text())
    data['runner']['completed_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    data['runner']['elapsed_wall_seconds'] = time.time() - started
    output.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()
