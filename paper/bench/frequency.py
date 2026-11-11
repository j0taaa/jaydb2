"""Linux policy snapshot, verified application/restoration, and sampled frequency."""
import argparse
import json
import os
from pathlib import Path
import time

CPU = Path('/sys/devices/system/cpu')


def observe():
    settings = {str(p): p.read_text().strip()
                for field in ('scaling_governor', 'energy_performance_preference')
                for p in sorted(CPU.glob('cpu[0-9]*/cpufreq/' + field))}
    turbo = CPU / 'intel_pstate/no_turbo'
    settings[str(turbo)] = turbo.read_text().strip()
    return dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), settings=settings,
                scaling_cur_freq_khz={str(p): int(p.read_text()) for p in sorted(CPU.glob('cpu[0-9]*/cpufreq/scaling_cur_freq'))},
                affinity_cpus=sorted(os.sched_getaffinity(0)),
                pinning='none; all engines inherit the same harness CPU affinity')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('capture', 'apply', 'restore'))
    parser.add_argument('snapshot', type=Path)
    args = parser.parse_args()
    if args.action == 'capture':
        with args.snapshot.open('x') as out:
            json.dump(observe(), out, indent=2)
        return
    original = json.loads(args.snapshot.read_text())['settings']
    desired = original if args.action == 'restore' else {
        p: '1' if p.endswith('/no_turbo') else 'performance' for p in original}
    errors = []
    # Restore governor before EPP: changing governor may itself reset EPP.
    for field in ('scaling_governor', 'energy_performance_preference', 'no_turbo'):
        for name, value in desired.items():
            if Path(name).name == field:
                try:
                    Path(name).write_text(value + '\n')
                except OSError as error:
                    errors.append(f'{name}: {error}')
    observed = observe()
    observed.update(action=args.action, verified=observed['settings'] == desired, errors=errors)
    print(json.dumps(observed, indent=2))
    if errors or not observed['verified']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
