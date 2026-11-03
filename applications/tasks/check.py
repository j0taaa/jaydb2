#!/usr/bin/env python3
"""One real session and three causal negatives; not part of the server/CI."""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

from app import ROOT, database, demonstrate, prepare

BAD_SEED = '''import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Policy.bend as P
import ./Configuration.bend as C

def state() -> D.State:
  D.State{[D.Table{"alice", [D.Row{"t0", [
    D.Field{"completed", D.VBool{False{}}}, D.Field{"id", D.VText{"t0"}},
    D.Field{"owner", D.VText{"alice"}}, D.Field{"title", D.VText{"without owner"}}]}]},
    D.Table{"bob", Nil{}}], [D.Row{"bob", [
      D.Field{"credential", D.VText{"bob-token"}}, D.Field{"id", D.VText{"bob"}},
      D.Field{"kind", D.VText{"user"}}]}]}

law structure_correct:
  {R.structure(C.config(), state()) == True{} : Bool}
def structure_correct():
  {==}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, L.Both{P.Both{P.Both{P.Both{{==}, {==}}, Unit{}},
    P.Both{Unit{}, Unit{}}}, Unit{}}}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database-root', type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.database_root.resolve()
    with tempfile.TemporaryFile() as errors:
        try:
            with database(root, stderr=errors) as db:
                demonstrate(db)
                assert db.call('token-invalid', ['list']) == {'status': 'authentication', 'value': None}
                target = 'S.Access{D.EnumerateKeys{D.Application{owner}}, listed}'
                assert db.code.count(target) == 1
                forbidden = db.code.replace(target,
                    'S.Access{D.EnumerateKeys{D.Application{"bob"}}, r => S.Refuse{D.VAbsent{}}}')
                assert db.call('alice-token', ['list'], code=forbidden) == {'status': 'certificate', 'value': None}
                owner = 'D.Field{"owner", D.VText{owner}}'
                assert db.code.count(owner) == 1
                forged = db.code.replace(owner, 'D.Field{"owner", D.VText{"ghost"}}')
                assert db.call('alice-token', ['save', 'fraud', 'do not publish', False], code=forged) == {'status': 'certificate', 'value': None}
                assert db.call('alice-token', ['list']) == {'status': 'success', 'value': []}
                assert db.call('bob-token', ['view', 't1']) == {'status': 'success', 'value': {
                    'completed': False, 'id': 't1', 'owner': 'bob', 'title': 'Review report'}}
        finally:
            if sys.exception() is not None:
                errors.seek(0)
                print(errors.read().decode("utf-8", "replace"), file=sys.stderr)
        errors.seek(0)
        diagnostics = errors.read()
        assert diagnostics.count(b'PRIMARY_CHECK') == 2, diagnostics.decode('utf-8', 'replace')
    with tempfile.TemporaryDirectory(prefix='jaydb-tasks-seed-') as tmp:
        directory = Path(tmp)
        prepare(directory, root)
        (directory / 'Seed.bend').write_text(BAD_SEED)
        result = subprocess.run([str(root / 'jaydb2'), '--configuration', str(directory / 'Configuration.bend'),
            '--seed', str(directory / 'Seed.bend')], cwd=root, input=b'', capture_output=True)
        assert (result.returncode and not result.stdout and b'PRIMARY_CHECK' in result.stderr
            and b'Location: initial_valid' in result.stderr), result.stderr.decode('utf-8', 'replace')
    print('PASS: CRUD, Alice/Bob isolation, refusal/rollback, authentication and three real proof negatives.')


if __name__ == '__main__':
    main()
