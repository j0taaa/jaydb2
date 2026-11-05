#!/usr/bin/env python3
"""Real admission/native receipt integration; run under the shared heavy lock."""
from contextlib import contextmanager
from pathlib import Path
import argparse
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
APP = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from applications.tasks.app import Database


def prepare(directory):
    for source in APP.glob('*.bend'):
        shutil.copyfile(source, directory / source.name)
    for name in ('Policy', 'Ownership', 'Proofs'):
        shutil.copyfile(ROOT / 'applications/tasks' / f'{name}.bend', directory / f'{name}.bend')
    for name in ('Orders', 'Foundations'):
        (directory / f'{name}.bend').write_text((ROOT / 'proof' / f'{name}.bend').read_text().replace('../contract/', './'))
    for name in ('Receipts', 'ReceiptLaws'):
        (directory / f'{name}.bend').write_text((ROOT / 'library' / f'{name}.bend').read_text().replace('../contract/', './'))


def proof_check(directory):
    # Development-only flat package: same module bodies, only relative imports
    # and generated open targets are replaced. Integration still uses real ones.
    for folder in ('contract', 'src'):
        for source in (ROOT / folder).glob('*.bend'):
            (directory / source.name).write_text(source.read_text().replace('../contract/', './'))
    (directory / 'Environment.bend').write_text('import Base\ndef identity() -> String:\n  "proof-development"\n')
    proof = (directory / 'ClientProof.bend').read_text()
    proof = proof[:proof.index('def B.certificate')]
    proof = proof.replace('import ./Instance.bend as I\n', '').replace('import ./Bindings.bend as B\n', '')
    (directory / 'ClientProof.bend').write_text(proof)
    (directory / 'Check.bend').write_text('import ./ClientProof.bend as ClientProof\nimport ./Seed.bend as Seed\n')
    subprocess.run([sys.executable, '-B', str(ROOT / 'tools/check.py'), str(directory / 'Check.bend')], check=True)
    prepare(directory)  # Actual integration uses the complete original proof.


@contextmanager
def session(directory, errors, *, storage=None, mode=None):
    command = [str(ROOT / 'jaydb2'), '--configuration', str(directory / 'Configuration.bend')]
    if mode != 'open':
        command += ['--seed', str(directory / 'Seed.bend')]
    if storage is not None:
        command += ['--storage', str(storage), '--storage-mode', mode]
    with subprocess.Popen(command, cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=errors, env={**os.environ, "TMPDIR": str(directory.parent.resolve())}) as process:
        try:
            yield Database(process, directory)
        finally:
            process.stdin.close()
            process.stdout.close()
    assert process.returncode == 0, process.returncode


def check_call(db, args, status='success', value=None, user='alice-token', **kw):
    actual = db.call(user, args, **kw)
    assert actual == {'status': status, 'value': value}, (args, actual, status, value)
    print(f'OK: {args[0]} -> {status}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument('--restart', action='store_true', help='Requires accepted persistence integration')
    args = parser.parse_args()
    build = ROOT / 'applications/vouchers/.build'
    build.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='check-', dir=build) as tmp, tempfile.TemporaryFile() as errors:
        directory = Path(tmp)
        prepare(directory)
        proof_check(directory)
        negatives = 0
        try:
            with session(directory, errors) as db:
                def call(*a, **kw):
                    check_call(db, *a, **kw)
                call(['issue', 'r1', 'coffee', False], value='v:r1')
                if not args.smoke:
                    call(['issue', 'r1', 'coffee', False], value='v:r1')
                    call(['issue', 'r1', 'tea', False], 'refusal', 'request conflict')
                    call(['issue', 'r1', 'coffee', True], 'refusal', 'request conflict')
                    call(['inspect', 'r1'], value='coffee')
                    call(['issue', 'r1', 'tea', False], value='v:r1', user='bob-token')
                    call(['permission', False], value='permission updated')
                    call(['issue', 'r1', 'coffee', False], 'refusal', 'permission denied')
                    call(['issue', 'fresh-denied', 'coffee', False], 'refusal', 'permission denied')
                    call(['permission', True], value='permission updated')
                    call(['issue', 'r1', 'coffee', False], value='v:r1')
                    call(['issue', 'cancel', 'discard', True], 'refusal', 'cancelled')
                    call(['inspect', 'cancel'], value=None)
                    call(['issue', 'cancel', 'different', False], value='v:cancel')
                    call(['retire', 'r1'], value='retired')
                    call(['inspect', 'r1'], value=None)
                    call(['issue', 'r1', 'new lifetime', False], value='v:r1')
                    call(['issue', '', 'Unicode: é\u0000🫖', False], value='v:')
                    call(['issue', '', 'Unicode: e\u0301\u0000🫖', False], 'refusal', 'request conflict')
                    call(['issue', 'r:v:permission', '0:1:', False], value='v:r:v:permission')
                    call(['issue', 'x'*64, 'boundary', False], value='v:'+'x'*64)
                    call(['issue', 'x'*65, 'too long', False], 'refusal', 'request ID too long')
                    call(['issue', 'r1', 'new lifetime', False], 'authentication', None, user='wrong')
                    # Every body uses the positive certificate: actual source binding,
                    # ownership and frozen protocol must reject these variations.
                    bodies = [
                        # Forged receipt without the business effect.
                        'S.Access{D.DefineRow{D.Application{D.context_id(ctx)}, "r:forged", '
                        'P.fields(D.context_id(ctx), "r:forged", "0:fraud", P.operation(), "invented")}, r => S.Finish{D.VText{"invented"}}}',
                        # Change an existing immutable receipt/result.
                        'S.Access{D.DefineRow{D.Application{D.context_id(ctx)}, "r:r1", '
                        'P.fields(D.context_id(ctx), "r:r1", "0:new lifetime", P.operation(), "changed")}, r => S.Finish{D.VText{"changed"}}}',
                        # Skip the present permission gate, including on hits.
                        'P.command(D.context_id(ctx), P.analyze(args))',
                        # Foreign reads remain forbidden even before refusal.
                        'S.Access{D.ReadCell{D.Application{"bob"}, "r:r1", "result"}, r => S.Refuse{D.VAbsent{}}}',
                        # Principal deletion/reuse is forbidden.
                        'S.Access{D.RemoveRow{D.Users{}, "alice"}, r => S.Finish{D.VAbsent{}}}',
                    ]
                    for body in bodies:
                        bad = db.code.replace('P.start(ctx, args)', body)
                        # Preserve affine use of ctx in the two direct writes.
                        bad = bad.replace('S.Program{ctx => args => ', 'S.Program{+ctx => args => ')
                        call(['issue', 'forged', 'fraud', False], 'certificate', None, code=bad)
                        negatives += 1
                    call(['inspect', 'forged'], value=None)
                    call(['issue', 'r1', 'new lifetime', False], value='v:r1')
            if not args.smoke:
                original = (directory / 'Configuration.bend').read_text()
                (directory / 'Configuration.bend').write_text(original.replace('32768n, 65536n, 32768n', '32768n, 2048n, 32768n'))
                with session(directory, errors) as db:
                    check_call(db, ['issue', 'large', 'a'*1200, False], 'limit')
                    check_call(db, ['inspect', 'large'])
                    check_call(db, ['issue', 'large', 'small', False], value='v:large')
                (directory / 'Configuration.bend').write_text(original.replace('32768n, 65536n, 32768n', '32768n, 65536n, 64n'))
                with session(directory, errors) as db:
                    check_call(db, ['issue', 'y'*64, 'oversized result', False], 'limit')
                    check_call(db, ['inspect', 'y'*64])
                    # Same ID with changed input reaches a second limit, not conflict.
                    check_call(db, ['issue', 'y'*64, 'changed', False], 'limit')
                (directory / 'Configuration.bend').write_text(original)
            if args.restart:
                storage = directory / 'storage'
                with session(directory, errors, storage=storage, mode='create') as db:
                    check_call(db, ['issue', 'persist', 'durable', False], value='v:persist')
                (directory / 'Seed.bend').unlink()  # Open must not reevaluate/reseed.
                with session(directory, errors, storage=storage, mode='open') as db:
                    check_call(db, ['issue', 'persist', 'durable', False], value='v:persist')
                    check_call(db, ['issue', 'persist', 'changed', False], 'refusal', 'request conflict')
                    check_call(db, ['inspect', 'persist'], value='durable')
            errors.seek(0)
            diagnostics = errors.read()
            assert diagnostics.count(b'PRIMARY_CHECK') == negatives, diagnostics.decode('utf-8', 'replace')
            if negatives:
                assert b'- expected :' in diagnostics and b'- observed :' in diagnostics
        finally:
            errors.seek(0)
            log = errors.read().decode('utf-8', 'replace')
            (build / 'diagnostics.log').write_text(log)
            if sys.exception() is not None:
                print(log, file=sys.stderr)
    print('PASS: certified receipt flow, law gates, permissions, conflicts, retirement and rollback'
          + ('; real restart survival' if args.restart else ''), flush=True)


if __name__ == '__main__':
    main()
