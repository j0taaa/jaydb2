#!/usr/bin/env python3
"""Copy a checked task-program template without changing JayDB2 or its laws."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'applications/tasks'))
import app
import query_check

CONCRETE = '''def B.certificate(s, valid, identity, n):
  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)'''
UNIVERSAL = '''def B.certificate(ctx, args, s, valid, identity, n):
  certify(ctx, args, B.code(), s, valid, identity, n)'''


def universal_proof(proof: str) -> str:
    """Use the existing parameterized lemma at the protocol's stronger target."""
    if proof.count(CONCRETE) != 1:
        raise ValueError('The template certificate wrapper changed; update the starter explicitly.')
    return proof.replace(CONCRETE, UNIVERSAL)


def create(destination: Path, profile: str = 'crud') -> Path:
    if profile not in ('crud', 'conditional'):
        raise ValueError('Profile must be crud or conditional')
    destination = destination.absolute()
    # Never merge generated files into an existing directory, including a symlink.
    if destination.exists() or destination.is_symlink():
        raise FileExistsError(f'Refusing to overwrite existing path: {destination}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.mkdir()
    if profile == 'crud':
        app.prepare(destination, ROOT)
    else:
        query_check.prepare(destination, ROOT)
    proof = (destination / 'ClientProof.bend').read_text()
    (destination / 'PreparedProof.bend').write_text(universal_proof(proof))
    original = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(destination.glob('*.bend'))}
    (destination / 'starter.json').write_text(json.dumps({
        'profile': profile,
        'template': 'applications/tasks',
        'exported_sha256': original,
    }, indent=2) + '\n')
    (destination / 'README.md').write_text('''# Your certified task application

These are copied application sources, not database changes. Start by reading
Client.bend, ClientProof.bend, Configuration.bend, Policy.bend and Seed.bend.
The other files reuse the existing ownership and prefix-composition modules.

ClientProof.bend supplies the ordinary per-call certificate. PreparedProof.bend
uses the SAME parameterized certify lemma under the documented universal
certificate binder; use it only with prepare (opcode 0), then execute the handle.
It does not grant additional permissions or bypass admission.

The `crud` profile supports list, view, save, conclude, remove and cancel.
The `conditional` profile supports pair, open, inspect, insert, replace_open,
cas and drop. Seed credentials alice-token/bob-token are public demo credentials.

From the JayDB2 checkout, validate the exported template before editing it:

    (ulimit -s unlimited
     flock /tmp/jaydb2-experiments-heavy.lock python3 -B examples/starter/check.py /absolute/path/to/this/directory)

See docs/programs-and-proofs.md in that checkout for the operation/proof map,
conditional updates, receipt examples and the limits of what these proofs show.
The check command is a development test; it is not part of database execution.
A source change requires a matching proof and another real admission check.
''')
    return destination


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    parser.add_argument('--profile', choices=('crud', 'conditional'), default='crud')
    args = parser.parse_args()
    try:
        destination = create(args.destination, args.profile)
    except (OSError, ValueError) as error:
        parser.exit(1, f'{error}\n')
    print(destination)


if __name__ == '__main__':
    main()
