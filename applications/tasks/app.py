#!/usr/bin/env python3
"""Task client for the real JayDB2; program and proof remain in Bend."""
from contextlib import contextmanager
import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile

APP = Path(__file__).resolve().parent
ROOT = APP.parents[1]
sys.path.insert(0, str(ROOT))
from tools.client import frame, unframe


def prepare(directory, root=ROOT):
    """Package the application and reuse two proof modules without duplicating them in the repository."""
    for source in APP.glob('*.bend'):
        shutil.copyfile(source, directory / source.name)
    for name in ('Orders', 'Foundations'):
        source = (root / 'proof' / f'{name}.bend').read_text()
        (directory / f'{name}.bend').write_text(source.replace('../contract/', './'))


class Database:
    def __init__(self, process, directory):
        self.process = process
        self.code = (directory / 'Client.bend').read_text()
        self.proof = (directory / 'ClientProof.bend').read_text()

    def call(self, credential, arguments, *, code=None):
        self.process.stdin.write(frame({'code': self.code if code is None else code,
            'proof': self.proof, 'credential': credential, 'arguments': arguments}))
        self.process.stdin.flush()
        header = self.process.stdout.read(8)
        if len(header) != 8:
            raise RuntimeError('The database exited before responding; inspect stderr.')
        body = self.process.stdout.read(int.from_bytes(header, 'big'))
        return unframe(header + body)


@contextmanager
def database(root=ROOT, *, stderr=None):
    with tempfile.TemporaryDirectory(prefix='jaydb-tasks-') as tmp:
        directory = Path(tmp)
        prepare(directory, root)
        with subprocess.Popen([str(root / 'jaydb2'), '--configuration', str(directory / 'Configuration.bend'),
                '--seed', str(directory / 'Seed.bend')], cwd=root, stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=stderr, start_new_session=True) as process:
            try:
                yield Database(process, directory)
            except BaseException:
                if process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                raise
            finally:
                try:
                    process.stdin.close()
                except BrokenPipeError:
                    pass
                process.stdout.close()
        if process.returncode:
            raise RuntimeError(f'The database exited with status {process.returncode}.')


def demonstrate(db):
    cases = [
        ('alice-token', ['save', 't1', 'Buy bread', False], {'status': 'success', 'value': 't1'}),
        ('alice-token', ['list'], {'status': 'success', 'value': ['t1']}),
        ('bob-token', ['list'], {'status': 'success', 'value': []}),
        ('bob-token', ['save', 't1', 'Review report', False], {'status': 'success', 'value': 't1'}),
        ('bob-token', ['view', 't1'], {'status': 'success', 'value': {
            'completed': False, 'id': 't1', 'owner': 'bob', 'title': 'Review report'}}),
        ('alice-token', ['view', 't1'], {'status': 'success', 'value': {
            'completed': False, 'id': 't1', 'owner': 'alice', 'title': 'Buy bread'}}),
        ('alice-token', ['cancel', 't1', 'do not publish', True], {'status': 'refusal', 'value': 'cancelled'}),
        ('alice-token', ['view', 't1'], {'status': 'success', 'value': {
            'completed': False, 'id': 't1', 'owner': 'alice', 'title': 'Buy bread'}}),
        ('alice-token', ['conclude', 't1'], {'status': 'success', 'value': 't1'}),
        ('alice-token', ['view', 't1'], {'status': 'success', 'value': {
            'completed': True, 'id': 't1', 'owner': 'alice', 'title': 'Buy bread'}}),
        ('alice-token', ['remove', 't1'], {'status': 'success', 'value': 't1'}),
        ('alice-token', ['list'], {'status': 'success', 'value': []}),
    ]
    for credential, args, expected in cases:
        response = db.call(credential, args)
        print(json.dumps({'user': credential.split('-')[0], 'command': args, 'response': response}, ensure_ascii=False), flush=True)
        assert response == expected, (args, response)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--demo', action='store_true', help='Run a real session and check its results')
    parser.add_argument('--database-root', type=Path, default=ROOT, help='Installed JayDB2 copy (default: this repository root)')
    args = parser.parse_args()
    with database(args.database_root.resolve()) as db:
        if args.demo:
            demonstrate(db)
            return
        credential = 'alice-token'
        print('Commands: list | view ID | save ID "title" [true|false] | cancel ID "title" [true|false] | conclude ID | remove ID | user TOKEN | exit')
        while True:
            try:
                words = shlex.split(input('tasks> '))
            except EOFError:
                break
            except ValueError as error:
                print(error)
                continue
            if not words:
                continue
            command, *values = words
            if command == 'exit':
                break
            if command == 'user' and len(values) == 1:
                credential = values[0]
                continue
            if command in ('save', 'cancel') and len(values) in (2, 3):
                if len(values) == 3 and values[2] not in ('true', 'false'):
                    print('Use true or false for completed.')
                    continue
                command = [command, *values[:2], len(values) == 3 and values[2] == 'true']
            elif (command == 'list' and not values) or (command in ('view', 'remove', 'conclude') and len(values) == 1):
                command = words
            else:
                print('Invalid command. Quote the title.')
                continue
            print(json.dumps(db.call(credential, command), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit(130)
