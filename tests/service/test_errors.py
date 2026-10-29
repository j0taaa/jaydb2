"""Compare the host's emergency frames with the immutable Bend contract."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bend import executable, environment
from tools.service.controller import error_frame


class ErrorFrameTests(unittest.TestCase):
    def test_all_six_frames_equal_contract(self):
        source = ('import Base\nimport ../../contrato/Semantica.bend as S\n'
                  'import ../../contrato/Protocolo.bend as P\n')
        for status, constructor in [('entrada', 'Entrada'), ('autenticacao', 'Autenticacao'),
            ('certificado', 'Certificado'), ('dados', 'Dados'), ('limite', 'Limite'), ('falha', 'Falha')]:
            value = ','.join(map(str, error_frame(status)))
            source += (f'\nlaw {status}:\n'
                f'  {{P.enquadrar(S.resposta_valor(S.resposta_erro(S.{constructor}{{}}))) == '
                f'Some{{[{value}]}} : Maybe<&2, List<&2, U32>>}}\n'
                f'def {status}():\n  {{==}}\n')
        (ROOT / 'build').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='errors-', dir=ROOT / 'build') as temp:
            file = Path(temp) / 'Erros.bend'
            file.write_text(source)
            for mode in ('--check-only', '--verdict'):
                checked = subprocess.run([str(executable()), str(file), mode],
                    env=environment(), capture_output=True, text=True, timeout=60)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                self.assertIn('ALL PROOFS CHECK', checked.stdout + checked.stderr)


if __name__ == '__main__':
    unittest.main()
