"""Check application proofs in one temporary copy of the public namespace."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
APP = ROOT / 'applications/vouchers'
sys.path.insert(0, str(ROOT))
from tools.bend import environment, executable


def check(runtime_directory):
    # Development verification never adds proof modules to the runtime package.
    # The actual host continues to receive the original complete ClientProof.
    with tempfile.TemporaryDirectory(prefix='proof-', dir=runtime_directory.parent) as temporary:
        directory = Path(temporary)
        environment_source = directory / 'Environment.bend'
        environment_source.write_text('import Base\ndef identity() -> String:\n  "proof-development"\n')
        builtin = {}
        for folder in ('contract', 'src'):
            builtin.update((path.name, path) for path in (ROOT / folder).glob('*.bend'))
        builtin.update((path.name, path) for path in APP.glob('*.bend'))
        for name in ('Policy', 'Ownership', 'Proofs'):
            builtin[f'{name}.bend'] = ROOT / f'applications/tasks/{name}.bend'
        for name in ('Receipts', 'ReceiptLaws', 'Laws', 'Query', 'Action'):
            builtin[f'{name}.bend'] = ROOT / f'library/{name}.bend'
        for name in ('Orders', 'Foundations'):
            builtin[f'{name}.bend'] = ROOT / f'proof/{name}.bend'
        builtin['Environment.bend'] = environment_source
        renamed = {
            ROOT / 'library/Proofs.bend': 'LibraryEventProofs.bend',
            APP / 'proof/VERIFY.bend': 'VoucherProofVerification.bend',
        }
        seen, names = {}, {}

        def visit(path):
            path = path.resolve()
            if path in seen:
                return seen[path]
            name = renamed.get(path, path.name)
            seen[path] = name
            source = path.read_text()
            if path == APP / 'ClientProof.bend':
                # Existing development-only open-target removal. Every actual
                # admission/native check below uses the unmodified original.
                source = source[:source.index('def B.certificate')]
                source = source.replace('import ./Instance.bend as I\n', '')
                source = source.replace('import ./Bindings.bend as B\n', '')

            def replace(match):
                dependency = (path.parent / match[1]).resolve()
                if not dependency.is_file():
                    dependency = builtin[Path(match[1]).name]
                return f'import ./{visit(dependency)} as {match[2]}'

            flat = re.sub(r'^import[ \t]+(\S+\.bend)[ \t]+as[ \t]+(\w+)[ \t]*$',
                          replace, source, flags=re.MULTILINE)
            strip = lambda text: ''.join(line for line in text.splitlines(keepends=True)
                                         if not line.startswith('import '))
            assert strip(source) == strip(flat), path
            if name in names and names[name] != flat:
                raise AssertionError(f'Conflicting public module: {path} -> {name}')
            names[name] = flat
            (directory / name).write_text(flat)
            return name

        entries = [APP / 'ClientProof.bend', APP / 'Seed.bend', APP / 'proof/VERIFY.bend']
        imports = [visit(path) for path in entries]
        rejected = [(path, visit(path)) for path in sorted((APP / 'proof/rejected').glob('*.bend'))]
        entry = directory / 'Check.bend'
        entry.write_text('import Base\n' + ''.join(
            f'import ./{name} as Checked{index}\n' for index, name in enumerate(imports)))
        subprocess.run([sys.executable, '-B', str(ROOT / 'tools/check.py'), str(entry),
                        str(ROOT / 'tests/service/ReceiptHelpers.bend')], check=True,
                       env={**os.environ, 'TMPDIR': str(directory.parent.resolve())})
        compiler = executable()
        for original, name in rejected:
            for mode in ('--check-only', '--verdict'):
                result = subprocess.run([str(compiler), str(directory / name), mode],
                                        env=environment(), capture_output=True, text=True, timeout=600)
                output = result.stdout + result.stderr
                intended = (result.returncode != 0 and 'SOME PROOFS FAIL' in output
                            and re.search(r'Location: false_\w+', output) is not None
                            and re.search(r'(?m)^\s*\d+>\| def false_', output) is not None
                            and '- expected :' in output and '- observed :' in output
                            and not any(error in output for error in (
                                'a defined name', 'a filled definition', 'a fresh name',
                                'a parsed term', 'stack overflow', 'consumed more than once')))
                if not intended:
                    raise AssertionError(f'Invalid false-proof control: {original} {mode}\n{output}')
                print(f'OK rejected {mode}: {original.relative_to(ROOT)}', flush=True)
