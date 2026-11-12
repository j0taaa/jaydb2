#!/usr/bin/env python3
"""Interleave Task A before/after sessions. Caller holds the heavy lock and runs
inside fixed-clock.sh. Build both trees first; the baseline may be a git archive.
This driver calls repeated_diagnose.capture unchanged in each tree.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
CAPTURE = r'''
import json
from pathlib import Path
import sys
from paper.bench import run
variant, calls, output, revision = sys.argv[1:]
if revision:
    # An archive inside ignored .build has no independent Git index. Inventory
    # its actual baseline revision, and label it rather than the parent HEAD.
    original_command = run.command
    def archive_command(*args):
        if args == ('git', 'ls-files'):
            return original_command('git', 'ls-tree', '--full-tree', '-r', '--name-only', revision)
        if args == ('git', 'rev-parse', 'HEAD'):
            return revision
        return original_command(*args)
    run.command = archive_command
from paper.bench.repeated_diagnose import capture
data = capture(int(calls))
data['variant'] = variant
if revision:
    data['metadata']['archive_revision'] = revision
Path(output).write_text(json.dumps(data, indent=2) + '\n')
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--baseline-revision', default='')
    parser.add_argument('--calls', type=int, default=100)
    parser.add_argument('--sessions', type=int, default=3)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.calls < 100 or args.sessions < 3:
        parser.error('final measurements require at least 100 calls and 3 sessions')
    if 'JAYDB_BENCH_FREQUENCY_ORIGINAL' not in os.environ:
        parser.error('run inside paper/bench/fixed-clock.sh while holding the heavy lock')
    baseline = args.baseline.resolve()
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    data = dict(before=[], after=[], order=[], harness='paper/bench/repeated_diagnose.py:capture',
                calls=args.calls, sessions=args.sessions, baseline_revision=args.baseline_revision)
    for sid in range(1, args.sessions + 1):
        for variant in (['before', 'after'] if sid % 2 else ['after', 'before']):
            tree = baseline if variant == 'before' else ROOT
            scratch = output.with_name(f'{output.stem}-{variant}-{sid}.json')
            revision = args.baseline_revision if variant == 'before' else ''
            subprocess.run([sys.executable, '-B', '-c', CAPTURE, variant, str(args.calls),
                            str(scratch), revision], cwd=tree, check=True)
            data[variant].append(json.loads(scratch.read_text()))
            data['order'].append(dict(session=sid, variant=variant))
            temporary = output.with_suffix(output.suffix + '.tmp')
            temporary.write_text(json.dumps(data, indent=2) + '\n')
            temporary.replace(output)
            print('paired', sid, variant, flush=True)


if __name__ == '__main__':
    main()
