#!/usr/bin/env python3
"""Check an exported starter in both official modes and a real prepared session.

Development only. The caller holds /tmp/jaydb2-experiments-heavy.lock, just as
for the existing native suites. No checker, runtime or administrator law changes.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bend import environment, executable
from tests.service.test_end_to_end import Server


def literal(text: str) -> str:
    return '"' + ''.join('\\"' if c == '"' else '\\\\' if c == '\\' else
                         f'\\u{{{ord(c):02x}}}' if ord(c) < 32 else c for c in text) + '"'


def stage(project: Path, directory: Path, code: str | None = None) -> None:
    for source in project.glob('*.bend'):
        shutil.copyfile(source, directory / source.name)
    if code is not None:
        (directory / 'Client.bend').write_text(code)
    (directory / 'ClientProof.bend').write_bytes((project / 'PreparedProof.bend').read_bytes())
    for folder in ('contract', 'src'):
        for source in (ROOT / folder).glob('*.bend'):
            (directory / source.name).write_text(source.read_text().replace('../contract/', './'))
    (directory / 'Environment.bend').write_text('import Base\ndef identity() -> String: "starter-development-check"\n')
    (directory / 'Instance.bend').write_text('import Base\nimport ./Configuration.bend as C\nimport ./Semantics.bend as S\ndef config() -> S.Configuration: C.config()\n')
    (directory / 'Bindings.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./RequestFacts.bend as F
import ./Instance.bend as I
import ./Client.bend as Client

def code() -> String:
  ''' + literal((directory / 'Client.bend').read_text()) + '''
law certificate:
  @ctx: D.Context -> @args: D.Value -> R.Certifies(I.config(), code(), Client.program(), ctx, args)
law terminates:
  F.ProgramTerminates(I.config(), Client.program())
''')
    (directory / 'Check.bend').write_text('import ./ClientProof.bend as Proof\nimport ./Seed.bend as Seed\n')


def mutants(profile: str, code: str) -> list[tuple[str, str]]:
    if profile == 'crud':
        cases = [
            ('forbidden-read', 'D.EnumerateKeys{D.Application{owner}}', 'D.EnumerateKeys{D.Application{"bob"}}'),
            ('forged-owner', 'D.Field{"owner", D.VText{owner}}', 'D.Field{"owner", D.VText{"ghost"}}'),
        ]
    else:
        cases = [
            ('forbidden-read', 'Q.select(D.Application{owner}, key, ["completed", "title"], projected(done))',
             'Q.select(D.Application{"bob"}, key, ["completed", "title"], projected(done))'),
            ('forbidden-write', 'M.compare_exchange(D.Application{owner}', 'M.compare_exchange(D.Application{"bob"}'),
        ]
    result = []
    for name, old, new in cases:
        if code.count(old) != 1:
            raise ValueError(f'Template changed at {name}; adapt this causal test to your actual operation.')
        result.append((name, code.replace(old, new)))
    return result


def pure_check(project: Path, profile: str, code: str, log: Path) -> list[tuple[str, str]]:
    changed = mutants(profile, code)
    with tempfile.TemporaryDirectory(prefix='starter-check-') as temporary, log.open('w') as output:
        for label, source in [('positive', code), *changed]:
            directory = Path(temporary) / label
            directory.mkdir()
            stage(project, directory, source)
            for mode in ('--check-only', '--verdict'):
                result = subprocess.run([str(executable()), str(directory / 'Check.bend'), mode],
                    capture_output=True, text=True, env=environment(), timeout=180)
                text = result.stdout + result.stderr
                output.write(f'=== {label} {mode} ===\n{text}\n'); output.flush()
                if label == 'positive':
                    if result.returncode or 'ALL PROOFS CHECK' not in text:
                        raise AssertionError(f'Positive starter failed {mode}; see {log}')
                else:
                    if not (result.returncode and 'SOME PROOFS FAIL' in text
                            and '- expected :' in text and '- observed :' in text):
                        raise AssertionError(f'Negative {label} did not fail at a proof obligation; see {log}')
                    if 'a defined name' in text or 'a filled definition' in text:
                        raise AssertionError(f'Negative {label} failed at missing source/proof; see {log}')
                print(f'PASS {label} {mode}', flush=True)
    return changed


def real_session(project: Path, profile: str, code: str, changed: list[tuple[str, str]], log: Path) -> None:
    proof = (project / 'PreparedProof.bend').read_text()
    server = Server(project, threads=1)
    try:
        prepared = server.prepared(0, code, 'alice-token', proof=proof)
        assert prepared['status'] == 'prepared', (prepared, server.diagnostics())
        handle = prepared['value']
        def call(args, value, credential='alice-token', status='success'):
            result = server.prepared(1, handle, credential, args)
            assert result == {'status': status, 'value': value}, (args, result, server.diagnostics())
        if profile == 'crud':
            call(['save', 't1', 'First task', False], 't1')
            call(['list'], ['t1'])
            call(['view', 't1'], {'completed': False, 'id': 't1', 'owner': 'alice', 'title': 'First task'})
            call(['list'], [], 'bob-token')
            call(['cancel', 't1', 'discard this', True], 'cancelled', status='refusal')
            call(['view', 't1'], {'completed': False, 'id': 't1', 'owner': 'alice', 'title': 'First task'})
            call(['conclude', 't1'], 't1')
            call(['view', 't1'], {'completed': True, 'id': 't1', 'owner': 'alice', 'title': 'First task'})
        else:
            call(['insert', 't1'], True)
            call(['insert', 't1'], False)
            call(['inspect', 't1'], {'completed': False, 'title': 'Once'})
            call(['inspect', 't1'], None, 'bob-token')
            call(['cas', 't1', True], False)
            call(['cas', 't1', False], True)
            call(['inspect', 't1'], {'completed': True, 'title': 'Replaced'})
        for label, source in changed:
            denied = server.prepared(0, source, 'alice-token', proof=proof)
            assert denied == {'status': 'certificate', 'value': None}, (label, denied, server.diagnostics())
        # Check the original handle and state after each denied source admission.
        if profile == 'crud':
            call(['view', 't1'], {'completed': True, 'id': 't1', 'owner': 'alice', 'title': 'First task'})
            call(['remove', 't1'], 't1')
            call(['list'], [])
        else:
            call(['inspect', 't1'], {'completed': True, 'title': 'Replaced'})
            call(['drop', 't1', 'missing'], None)
            call(['inspect', 't1'], None)
        server.finish()
    finally:
        log.write_text(server.diagnostics())
        server.close()
    print(f'PASS real {profile} prepared session, source negatives and unchanged-state followups', flush=True)


def check(project: Path) -> None:
    project = project.resolve()
    metadata = json.loads((project / 'starter.json').read_text())
    profile = metadata['profile']
    if profile not in ('crud', 'conditional'):
        raise ValueError('Unknown starter profile')
    code = (project / 'Client.bend').read_text()
    logs = project / '.check'
    logs.mkdir(exist_ok=True)
    changed = pure_check(project, profile, code, logs / 'proofs.txt')
    real_session(project, profile, code, changed, logs / 'service.txt')
    print(f'PASS starter {profile}: both official modes, real execution and source-bound law rejection; logs in {logs}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', nargs='?', type=Path)
    parser.add_argument('--all', action='store_true', help='Check freshly exported copies of both supplied profiles')
    args = parser.parse_args()
    if bool(args.project) == args.all:
        parser.error('Supply either PROJECT or --all')
    if args.project:
        check(args.project)
        return
    from create import create
    output = ROOT / 'build/starter'
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='profiles-', dir=output) as temporary:
        for profile in ('crud', 'conditional'):
            project = create(Path(temporary) / profile, profile)
            try:
                check(project)
            finally:
                logs = project / '.check'
                if logs.is_dir():
                    shutil.copytree(logs, output / profile, dirs_exist_ok=True)
    print(f'PASS both exported profiles; retained proof/service logs in {output}')


if __name__ == '__main__':
    main()
