"""Launch the service under the native allocation observer.

This is an integration/probe entrypoint. It never converts an incomplete
observation, internal capacity refusal, or tracer failure into public limite.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
from .build import build


def run(command, report, *, timeout=30, output=None, service_window=False, stage_control=False):
    _, tracer = build() if output is None else (None, Path(output) / 'jayacct-trace')
    result = subprocess.run([str(tracer), '--report', str(report),
                            *(['--service-window'] if service_window else []),
                            *(['--stage-control'] if stage_control else []), '--', *map(str, command)],
                            capture_output=True, timeout=timeout)
    records = [json.loads(line) for line in Path(report).read_text().splitlines()]
    return result, records


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--service-window', action='store_true')
    parser.add_argument('--stage-control', action='store_true')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    result, _ = run(command, args.report, timeout=args.timeout, service_window=args.service_window,stage_control=args.stage_control)
    print(result.stdout.decode(), end='')
    print(result.stderr.decode(), end='', file=__import__('sys').stderr)
    raise SystemExit(result.returncode)
