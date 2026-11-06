#!/usr/bin/env python3
"""Task client for the real JayDB2; program and proof remain in Bend."""
from contextlib import contextmanager, ExitStack
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
    for name in ('Laws', 'Query', 'Action'):
        source = (root / 'library' / f'{name}.bend').read_text()
        (directory / f'{name}.bend').write_text(source.replace('../contract/', './').replace('../src/', './'))


def workspace_directory(workspace, mode, root=ROOT):
    """Create a frozen example package once; reopening never copies a seed/source."""
    workspace = Path(workspace).resolve()
    if mode == 'create':
        workspace.mkdir(parents=True, mode=0o700)
        directory = workspace / 'app'
        directory.mkdir(mode=0o700)
        prepare(directory, root)
    elif mode == 'open':
        directory = workspace / 'app'
        for name in ('Configuration.bend', 'Client.bend', 'ClientProof.bend'):
            if not (directory / name).is_file():
                raise ValueError(f'Missing task workspace file: {directory / name}. Use create only for a new workspace.')
    else:
        raise ValueError('Storage mode must be create or open.')
    return directory


class Database:
    def __init__(self, process, directory):
        self.process = process
        self.code = (directory / 'Client.bend').read_text()
        self.proof = (directory / 'ClientProof.bend').read_text()

    def call(self, credential, arguments, *, code=None):
        try:
            self.process.stdin.write(frame({'code': self.code if code is None else code,
                'proof': self.proof, 'credential': credential, 'arguments': arguments}))
            self.process.stdin.flush()
        except BrokenPipeError as error:
            raise RuntimeError('The database closed during the request; its write outcome may be unknown. Inspect stderr before retrying.') from error
        header = self.process.stdout.read(8)
        if len(header) != 8:
            raise RuntimeError('The database closed without a complete response; its write outcome may be unknown. Inspect stderr before retrying.')
        body = self.process.stdout.read(int.from_bytes(header, 'big'))
        try:
            return unframe(header + body)
        except ValueError as error:
            raise RuntimeError('Invalid or incomplete database response; its write outcome may be unknown. Inspect stderr before retrying.') from error


@contextmanager
def database(root=ROOT, *, stderr=None, workspace=None, storage_mode=None, threads=None):
    root = Path(root).resolve()
    if (workspace is None) != (storage_mode is None):
        raise ValueError('Use workspace and storage_mode together.')
    with ExitStack() as stack:
        if workspace is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix='jaydb-tasks-')))
            prepare(directory, root)
        else:
            workspace = Path(workspace).resolve()
            directory = workspace_directory(workspace, storage_mode, root)
        command = [str(root / 'jaydb2'), '--configuration', str(directory / 'Configuration.bend')]
        if storage_mode != 'open':
            command += ['--seed', str(directory / 'Seed.bend')]
        if workspace is not None:
            command += ['--storage', str(workspace / 'db'), '--storage-mode', storage_mode]
        if threads is not None:
            command += ['--threads', str(threads)]
        with subprocess.Popen(command, cwd=root, stdin=subprocess.PIPE,
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
    parser.add_argument('--workspace', type=Path, help='Persistent task workspace (app sources and db image)')
    parser.add_argument('--storage-mode', choices=('create', 'open'), help='Create a new workspace or open its existing database; never resets data')
    parser.add_argument('--credential', default='alice-token', help='Credential sent on every request (default: public example alice-token)')
    parser.add_argument('--threads', type=int, default=1, help='Native workers for this small example (default: 1)')
    parser.add_argument('--command', nargs=argparse.REMAINDER, help='Run one task command and exit; place all options before this flag')
    args = parser.parse_args()
    if (args.workspace is None) != (args.storage_mode is None):
        parser.error('--workspace and --storage-mode are required together')
    if args.demo and (args.workspace is not None or args.command is not None):
        parser.error('--demo uses its own disposable volatile session')
    if not 1 <= args.threads <= 128:
        parser.error('--threads must be from 1 to 128')
    command = None
    if args.command is not None:
        try:
            command = task_command(args.command)
        except ValueError as error:
            parser.error(str(error))
    with database(args.database_root.resolve(), workspace=args.workspace,
                  storage_mode=args.storage_mode, threads=args.threads) as db:
        if args.demo:
            demonstrate(db)
            return
        if command is not None:
            response = db.call(args.credential, command)
            print(json.dumps(response, ensure_ascii=False))
            return 0 if response['status'] == 'success' else 2
        credential = args.credential
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
            try:
                command = task_command(words)
            except ValueError as error:
                print(error)
                continue
            print(json.dumps(db.call(credential, command), ensure_ascii=False, indent=2))


def task_command(words):
    if not words:
        raise ValueError('Supply a command: list, view, save, cancel, conclude or remove.')
    command, *values = words
    if command in ('save', 'cancel') and len(values) in (2, 3):
        if len(values) == 3 and values[2] not in ('true', 'false'):
            raise ValueError('Use true or false for completed.')
        return [command, *values[:2], len(values) == 3 and values[2] == 'true']
    if (command == 'list' and not values) or (command in ('view', 'remove', 'conclude') and len(values) == 1):
        return list(words)
    raise ValueError('Invalid task command. Quote the title and check the argument count.')


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
    except (OSError, RuntimeError, ValueError) as error:
        print(f'tasks: {error}', file=sys.stderr)
        raise SystemExit(1)
