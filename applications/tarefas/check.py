#!/usr/bin/env python3
"""Uma sessão real e três negativos causais; não participa do servidor/CI."""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

from app import ROOT, banco, demonstrar, preparar

BAD_SEED = '''import Base
import ./Dados.bend as D
import ./Requisitos.bend as R
import ./Logica.bend as L
import ./Policy.bend as P
import ./Configuration.bend as C

def estado() -> D.Estado:
  D.Estado{[D.Tabela{"alice", [D.Linha{"t0", [
    D.Campo{"concluida", D.VBool{False{}}}, D.Campo{"id", D.VTexto{"t0"}},
    D.Campo{"proprietario", D.VTexto{"alice"}}, D.Campo{"titulo", D.VTexto{"sem dono"}}]}]},
    D.Tabela{"bob", Nil{}}], [D.Linha{"bob", [
      D.Campo{"credencial", D.VTexto{"bob-token"}}, D.Campo{"id", D.VTexto{"bob"}},
      D.Campo{"tipo", D.VTexto{"usuario"}}]}]}

law estrutura_correta:
  {R.estrutura(C.config(), estado()) == True{} : Bool}
def estrutura_correta():
  {==}

law inicial_valido:
  R.Valido(C.config(), estado())
def inicial_valido():
  L.Ambos{{==}, L.Ambos{P.Ambos{P.Ambos{P.Ambos{{==}, {==}}, Unit{}},
    P.Ambos{Unit{}, Unit{}}}, Unit{}}}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database-root', type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.database_root.resolve()
    with tempfile.TemporaryFile() as errors:
        try:
            with banco(root, stderr=errors) as db:
                demonstrar(db)
                assert db.call('token-invalido', ['listar']) == {'status': 'autenticacao', 'valor': None}
                target = 'S.Acessar{D.EnumerarChaves{D.Aplicacao{proprietario}}, listado}'
                assert db.code.count(target) == 1
                forbidden = db.code.replace(target,
                    'S.Acessar{D.EnumerarChaves{D.Aplicacao{"bob"}}, r => S.Recusar{D.VAusente{}}}')
                assert db.call('alice-token', ['listar'], code=forbidden) == {'status': 'certificado', 'valor': None}
                owner = 'D.Campo{"proprietario", D.VTexto{proprietario}}'
                assert db.code.count(owner) == 1
                forged = db.code.replace(owner, 'D.Campo{"proprietario", D.VTexto{"fantasma"}}')
                assert db.call('alice-token', ['salvar', 'fraude', 'não publicar', False], code=forged) == {'status': 'certificado', 'valor': None}
                assert db.call('alice-token', ['listar']) == {'status': 'sucesso', 'valor': []}
                assert db.call('bob-token', ['ver', 't1']) == {'status': 'sucesso', 'valor': {
                    'concluida': False, 'id': 't1', 'proprietario': 'bob', 'titulo': 'Revisar relatório'}}
        finally:
            if sys.exception() is not None:
                errors.seek(0)
                print(errors.read().decode("utf-8", "replace"), file=sys.stderr)
        errors.seek(0)
        diagnostics = errors.read()
        assert diagnostics.count(b'PRIMARY_CHECK') == 2, diagnostics.decode('utf-8', 'replace')
    with tempfile.TemporaryDirectory(prefix='jaydb-tarefas-seed-') as tmp:
        directory = Path(tmp)
        preparar(directory, root)
        (directory / 'Seed.bend').write_text(BAD_SEED)
        result = subprocess.run([str(root / 'jaydb2'), '--configuration', str(directory / 'Configuration.bend'),
            '--seed', str(directory / 'Seed.bend')], cwd=root, input=b'', capture_output=True)
        assert (result.returncode and not result.stdout and b'PRIMARY_CHECK' in result.stderr
            and b'Location: inicial_valido' in result.stderr), result.stderr.decode('utf-8', 'replace')
    print('PASS: CRUD, isolamento Alice/Bob, recusa/rollback, autenticação e três negativos reais de prova.')


if __name__ == '__main__':
    main()
