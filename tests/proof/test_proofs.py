#!/usr/bin/env python3
"""Causal negative controls; `make verify` checks the positive aggregates."""
from pathlib import Path
import argparse
import json
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bend import environment, executable
sys.path.insert(0, str(ROOT / "tools"))
from check import COVERAGE_AREAS, check_coverage


def coverage_controls():
    """An orphaned module or missing import must fail before proof checking."""
    with tempfile.TemporaryDirectory(prefix="jaydb-coverage-") as temporary:
        root = Path(temporary)
        for area in COVERAGE_AREAS:
            (root / area).mkdir()
            (root / area / "Included.bend").write_text("import Base\n")
        (root / "src/Included.bend").write_text("import Base # pinned\nimport ../library/Included.bend as Library\n")
        (root / "proof/Included.bend").write_text("import ../src/Included.bend as Source\n")
        entry = root / "VERIFY.bend"
        imports = "import ./proof/Included.bend as Proof\nimport ./contract/Included.bend as Contract\n"
        entry.write_text("# header comment\n\n" + imports + "def body() -> Unit:\n  Unit{}\n")
        report = check_coverage([entry], root)
        assert all(count["modules"] == 1 for count in report["areas"].values())
        assert len(report["modules"]) == len(COVERAGE_AREAS) + 1
        for area in COVERAGE_AREAS:
            orphan = root / area / "Orphan.bend"
            orphan.write_text("import Base\n")
            try:
                check_coverage([entry], root)
            except RuntimeError as error:
                assert "outside verification roots" in str(error) and f"{area}/Orphan.bend" in str(error)
            else:
                raise AssertionError(f"Unverified {area} module escaped the coverage gate")
            orphan.unlink()
        for header, expected in ((imports + "import ./Missing.bend as Missing\n", "Missing verification module"),
                                 ("import remote_package as Remote\n", "Unsupported verification import"),
                                 ("import ../Outside.bend as Outside\n", "escapes the repository")):
            entry.write_text(header)
            try:
                check_coverage([entry], root)
            except RuntimeError as error:
                assert expected in str(error), str(error)
            else:
                raise AssertionError(f"Invalid coverage graph was accepted: {header}")
    print("OK import-coverage positive and negative controls", flush=True)


def positive_bindings():
    """Keep the checked fixture bound to the real application's exact bodies."""
    package = ROOT / 'tests/proof/tasks'
    relocations = {'Data': 'contract', 'Semantics': 'contract', 'Logic': 'contract',
                   'Requirements': 'contract', 'Termination': 'src', 'ValidationFinal': 'src',
                   'Laws': 'library', 'Orders': 'proof'}
    for name in ('Configuration', 'Seed', 'Client', 'ClientProof', 'Policy', 'Proofs', 'Ownership'):
        expected = (ROOT / 'applications/tasks' / (name + '.bend')).read_text()
        for module, area in relocations.items():
            expected = expected.replace(f'import ./{module}.bend as ', f'import ../../../{area}/{module}.bend as ')
        assert (package / (name + '.bend')).read_text() == expected, f'Tasks fixture drift: {name}'
    bindings = (package / 'Bindings.bend').read_text()
    for function, module in (('code', 'Client'), ('proof_source', 'ClientProof')):
        literal = re.search(r'def ' + function + r'\(\) -> String:\n  ("(?:[^"\\]|\\.)*")', bindings)
        assert literal and json.loads(literal[1]) == (package / (module + '.bend')).read_text(), function
    print('OK tasks source/proof literal bindings', flush=True)


def implementation_mutations():
    """Tie negatives to real bodies and original universal theorem statements."""
    def relocate(text):
        return (text.replace('import ../contract/', 'import ../../../contract/')
                    .replace('import ../proof/', 'import ../../../proof/')
                    .replace('import ./', 'import ../../../src/'))

    def mutate_once(text, old, new):
        assert text.count(old) == 1, f'Mutation target drift: {old}'
        return text.replace(old, new)

    limits = relocate((ROOT / 'src/LimitWords.bend').read_text())
    limits = mutate_once(limits, 'select(B.Number64{0, 65536}, blocks(256n, n), n)',
                            'select(B.Number64{0, 65535}, blocks(256n, n), n)')
    limits = limits.replace('law convert_equals_reference:', 'law false:').replace(
        'def convert_equals_reference(n):', 'def false(n):')
    expected = {'LimitWordsMutatedConvert.bend': limits}
    worker = relocate((ROOT / 'src/Worker.bend').read_text())
    bridge = (ROOT / 'proof/WorkerBridge.bend').read_text()
    metadata = bridge[bridge.index('def prepared_metadata('):bridge.index('# The constant guard')]
    metadata = metadata.replace('W.ready_metadata(', 'ready_metadata(')
    for name, law_name, old, new in (
        ('WorkerMutatedPrincipal.bend', 'prepared_principal_is_same_fresh_dispatch_authentication',
         'Input.identity(authentication, s, raw)', 'Input.identity(Some{D.Context{"spoofed", "user"}}, s, raw)'),
        ('WorkerMutatedRoute.bend', 'prepared_route_is_checked_raw_handle',
         'Some{Gate.code(raw)}', 'Some{"wrong-handle"}')):
        start = bridge.index('law ' + law_name + ':')
        end = bridge.find('\nlaw ', start + 1)
        if name == 'WorkerMutatedPrincipal.bend':
            end = bridge.index('\ndef reference(', start)
        law = bridge[start:end].replace('law ' + law_name + ':', 'law false:').replace(
            'def ' + law_name + '(', 'def false(')
        expected[name] = mutate_once(worker, old, new) + '\n' + metadata + law
    for name, body in expected.items():
        file = ROOT / 'tests/proof/rejected' / name
        assert file.read_text() == body, f'Implementation mutation fixture drift: {name}'
    print('OK implementation mutations bound to actual bodies and universal laws', flush=True)
    return [ROOT / 'tests/proof/rejected' / name for name in expected]


def only_false_fails(output):
    # Check every diagnostic location, including failures in imported helpers.
    locations = re.findall(r'^Location:\s*(\S+)\s*$', output, re.MULTILINE)
    return bool(locations) and set(locations) == {'false'}


def diagnostic_controls():
    assert only_false_fails('Location: false\n')
    assert not only_false_fails('Location: false_handle_is_original_source\n')
    assert not only_false_fails('Location: false\nLocation: certificate\n')
    assert not only_false_fails('Location: certificate\nLocation: false\n')
    assert not only_false_fails('SOME PROOFS FAIL\n')
    print('OK negative diagnostic-location controls', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--implementation-mutations-only', action='store_true')
    args = parser.parse_args()
    diagnostic_controls()
    mutations = implementation_mutations()
    if not args.implementation_mutations_only:
        coverage_controls()
        positive_bindings()
    # Each mutation removes a different premise: bytes, administrative law,
    # publishable state, authentication, construction guard, or reification.
    compiler = executable()
    count = 0
    paths = mutations if args.implementation_mutations_only else Path(__file__).with_name('rejected').glob('*.bend')
    for path in sorted(paths):
        for mode in ('--check-only', '--verdict'):
            run = subprocess.run([str(compiler), str(path), mode],
                cwd=ROOT, env=environment(), capture_output=True, text=True, timeout=600)
            output = run.stdout + run.stderr
            if not (run.returncode and 'SOME PROOFS FAIL' in output
                    and only_false_fails(output)
                    and '- expected :' in output
                    and '- observed :' in output and 'a defined name' not in output
                    and 'a filled definition' not in output):
                raise AssertionError(f'Expected a false proof, not a broken fixture: {path} {mode}\n{output}')
            print(f'OK rejected {mode}: {path.relative_to(ROOT)}', flush=True)
        count += 1
    print(f'OK negative controls: {count} fixtures, {count * 2} official-mode rejections', flush=True)


if __name__ == '__main__':
    main()
