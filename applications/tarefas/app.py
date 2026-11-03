#!/usr/bin/env python3
"""Cliente de tarefas para o JayDB2 real; programa e prova ficam em Bend."""
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


def preparar(directory, root=ROOT):
    """Empacota a aplicação e reutiliza dois módulos de prova, sem copiá-los no repo."""
    for source in APP.glob('*.bend'):
        shutil.copyfile(source, directory / source.name)
    for name in ('Ordens', 'Fundamentos'):
        source = (root / 'proof' / f'{name}.bend').read_text()
        (directory / f'{name}.bend').write_text(source.replace('../contrato/', './'))


class Banco:
    def __init__(self, process, directory):
        self.process = process
        self.code = (directory / 'Client.bend').read_text()
        self.proof = (directory / 'ClientProof.bend').read_text()

    def call(self, credential, arguments, *, code=None):
        self.process.stdin.write(frame({'codigo': self.code if code is None else code,
            'prova': self.proof, 'credencial': credential, 'argumentos': arguments}))
        self.process.stdin.flush()
        header = self.process.stdout.read(8)
        if len(header) != 8:
            raise RuntimeError('O banco encerrou antes da resposta; consulte stderr.')
        body = self.process.stdout.read(int.from_bytes(header, 'big'))
        return unframe(header + body)


@contextmanager
def banco(root=ROOT, *, stderr=None):
    with tempfile.TemporaryDirectory(prefix='jaydb-tarefas-') as tmp:
        directory = Path(tmp)
        preparar(directory, root)
        with subprocess.Popen([str(root / 'jaydb2'), '--configuration', str(directory / 'Configuration.bend'),
                '--seed', str(directory / 'Seed.bend')], cwd=root, stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=stderr, start_new_session=True) as process:
            try:
                yield Banco(process, directory)
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
            raise RuntimeError(f'O banco encerrou com status {process.returncode}.')


def demonstrar(db):
    cases = [
        ('alice-token', ['salvar', 't1', 'Comprar pão', False], {'status': 'sucesso', 'valor': 't1'}),
        ('alice-token', ['listar'], {'status': 'sucesso', 'valor': ['t1']}),
        ('bob-token', ['listar'], {'status': 'sucesso', 'valor': []}),
        ('bob-token', ['salvar', 't1', 'Revisar relatório', False], {'status': 'sucesso', 'valor': 't1'}),
        ('bob-token', ['ver', 't1'], {'status': 'sucesso', 'valor': {
            'concluida': False, 'id': 't1', 'proprietario': 'bob', 'titulo': 'Revisar relatório'}}),
        ('alice-token', ['ver', 't1'], {'status': 'sucesso', 'valor': {
            'concluida': False, 'id': 't1', 'proprietario': 'alice', 'titulo': 'Comprar pão'}}),
        ('alice-token', ['cancelar', 't1', 'não publicar', True], {'status': 'recusa', 'valor': 'cancelado'}),
        ('alice-token', ['ver', 't1'], {'status': 'sucesso', 'valor': {
            'concluida': False, 'id': 't1', 'proprietario': 'alice', 'titulo': 'Comprar pão'}}),
        ('alice-token', ['concluir', 't1'], {'status': 'sucesso', 'valor': 't1'}),
        ('alice-token', ['ver', 't1'], {'status': 'sucesso', 'valor': {
            'concluida': True, 'id': 't1', 'proprietario': 'alice', 'titulo': 'Comprar pão'}}),
        ('alice-token', ['remover', 't1'], {'status': 'sucesso', 'valor': 't1'}),
        ('alice-token', ['listar'], {'status': 'sucesso', 'valor': []}),
    ]
    for credential, args, expected in cases:
        response = db.call(credential, args)
        print(json.dumps({'usuario': credential.split('-')[0], 'pedido': args, 'resposta': response}, ensure_ascii=False), flush=True)
        assert response == expected, (args, response)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--demo', action='store_true', help='Executa uma sessão real e confere seus resultados')
    parser.add_argument('--database-root', type=Path, default=ROOT, help='Copia instalada do JayDB2 (padrao: raiz deste repositorio)')
    args = parser.parse_args()
    with banco(args.database_root.resolve()) as db:
        if args.demo:
            demonstrar(db)
            return
        credential = 'alice-token'
        print('Comandos: listar | ver ID | salvar ID "título" [true|false] | cancelar ID "título" [true|false] | concluir ID | remover ID | usuario TOKEN | sair')
        while True:
            try:
                words = shlex.split(input('tarefas> '))
            except EOFError:
                break
            except ValueError as error:
                print(error)
                continue
            if not words:
                continue
            command, *values = words
            if command == 'sair':
                break
            if command == 'usuario' and len(values) == 1:
                credential = values[0]
                continue
            if command in ('salvar', 'cancelar') and len(values) in (2, 3):
                if len(values) == 3 and values[2] not in ('true', 'false'):
                    print('Use true ou false para concluída.')
                    continue
                pedido = [command, *values[:2], len(values) == 3 and values[2] == 'true']
            elif (command == 'listar' and not values) or (command in ('ver', 'remover', 'concluir') and len(values) == 1):
                pedido = words
            else:
                print('Comando inválido. Use aspas no título.')
                continue
            print(json.dumps(db.call(credential, pedido), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit(130)
