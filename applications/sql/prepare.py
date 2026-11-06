#!/usr/bin/env python3
"""Package the SQL task policy adapter without changing the engine or its laws."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'applications' / 'tasks'))
import app


def prepare(directory: Path, root: Path = ROOT) -> None:
    # Reuse exactly the checked task policy, initial-state proof and dependencies.
    app.prepare(directory, root)
    # Generated multirow programs carry code and a universal certificate.
    # This changes only the public message ceiling, never the ownership law.
    configuration = directory / 'Configuration.bend'
    source = configuration.read_text()
    previous = 'S.Limits{32768n, 65536n, 32768n}'
    if source.count(previous) != 1:
        raise ValueError('Task fixture limits changed; review SQL package limits')
    configuration.write_text(source.replace(previous, 'S.Limits{131072n, 65536n, 32768n}'))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=False)
    prepare(args.directory)


if __name__ == '__main__':
    main()
