#!/usr/bin/env python3
"""Optional query modules in an ordinary real task session."""
from pathlib import Path
import argparse
import subprocess
import sys
import tempfile

import app


def prepare(directory, root):
    app.prepare(directory, root)
    # Explicit opt-in public dependency closure; the normal client is unchanged.
    (directory / 'Task.bend').write_text((app.APP / 'Client.bend').read_text())
    for name in ('Action', 'Query'):
        source = (app.ROOT / 'library' / f'{name}.bend').read_text()
        (directory / f'{name}.bend').write_text(source.replace('../contract/', './'))
    configuration = (directory / 'Configuration.bend').read_text()
    configuration = 'import ./Query.bend as Query\nimport ./Action.bend as Action\nimport ./Task.bend as Task\n' + configuration
    (directory / 'Configuration.bend').write_text(configuration)
    (directory / 'Client.bend').write_text((app.APP / 'QueryClient.bend').read_text())
    (directory / 'ClientProof.bend').write_text((app.APP / 'QueryClientProof.bend').read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database-root', type=Path, default=app.ROOT)
    args = parser.parse_args()
    root = args.database_root.resolve()
    with tempfile.TemporaryDirectory(prefix='jaydb-query-') as tmp, tempfile.TemporaryFile() as errors:
        directory = Path(tmp)
        prepare(directory, root)
        try:
            with subprocess.Popen([str(root / 'jaydb2'), '--configuration', str(directory / 'Configuration.bend'),
                    '--seed', str(directory / 'Seed.bend')], cwd=root, stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, stderr=errors) as process:
                db = app.Database(process, directory)
                ordinary = app.Database(process, directory)
                ordinary.code = (app.APP / 'Client.bend').read_text()
                ordinary.proof = (app.APP / 'ClientProof.bend').read_text()
                def call(credential, arguments, expected, **kw):
                    response = db.call(credential, arguments, **kw)
                    assert response == expected, (arguments, response, expected)
                call('alice-token', ['pair', 't1', 't2', False], {'status': 'success', 'value': 't1'})
                assert ordinary.call('alice-token', ['view', 't2']) == {'status': 'success', 'value': {
                    'completed': True, 'id': 't2', 'owner': 'alice', 'title': 'Second'}}
                call('alice-token', ['open', 't1', 't2'], {'status': 'success', 'value': [{'title': 'First'}]})
                call('alice-token', ['open', 't2', 'missing'], {'status': 'success', 'value': []})
                call('bob-token', ['open', 't1', 't2'], {'status': 'success', 'value': []})
                call('alice-token', ['pair', 't2', 't3', True], {'status': 'refusal', 'value': 'cancelled'})
                call('alice-token', ['open', 't2', 't3'], {'status': 'success', 'value': []})
                assert ordinary.call('alice-token', ['view', 't2']) == {'status': 'success', 'value': {
                    'completed': True, 'id': 't2', 'owner': 'alice', 'title': 'Second'}}
                assert ordinary.call('alice-token', ['view', 't3']) == {'status': 'success', 'value': None}
                target = 'Q.select(D.Application{owner}, key, ["completed", "title"], projected(done))'
                assert db.code.count(target) == 1
                # Same selected reads as the positive flow, now on Bob's table;
                # an eventual refusal cannot authorize the earlier read.
                forbidden = db.code.replace(target,
                    'Q.select(D.Application{"bob"}, key, ["completed", "title"], result => S.Refuse{D.VAbsent{}})')
                call('alice-token', ['open', 't1', 't2'], {'status': 'certificate', 'value': None}, code=forbidden)
                call('alice-token', ['open', 't1', 't2'], {'status': 'success', 'value': [{'title': 'First'}]})
                process.stdin.close()
                process.stdout.close()
            assert process.returncode == 0, process.returncode
        finally:
            if sys.exception() is not None:
                errors.seek(0)
                print(errors.read().decode('utf-8', 'replace'), file=sys.stderr)
        errors.seek(0)
        diagnostics = errors.read()
        assert (diagnostics.count(b'PRIMARY_CHECK') == 1 and b'- expected :' in diagnostics
            and b'- observed :' in diagnostics and b'Location: visit_safe' in diagnostics), diagnostics.decode('utf-8', 'replace')
    print('PASS: selected fields, filtering/projection, missing rows, ownership, pair writes, refusal rollback, prohibited-read proof rejection.')


if __name__ == '__main__':
    main()
