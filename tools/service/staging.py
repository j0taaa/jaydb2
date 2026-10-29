"""Freeze the public environment and generate checked native entry modules.

The published database is never written to these directories. Client source is
copied byte for byte; only the repository's own imports are relocated.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import posixpath
import re
from types import MappingProxyType

ROOT = Path(__file__).resolve().parents[2]
INSTALL_ROOT = ROOT
VERIFIER_BINARY = 'tools/verifier/installed/bendtt-budget'
VERIFIER_MANIFEST = 'tools/verifier/installed/manifest.json'
SERVICE_TOOLING = frozenset({
    'abi_simple.py', 'controller.py', 'entry.py', 'frames.py', 'isolated.py',
    'staging.py', 'compile.mjs', 'naturals.py', 'paired_loading.py',
    'loading.py', 'loading.c', 'loading.h', 'build_loading.py',
    'lifecycle.py', 'lifecycle.c', 'lifecycle.h', 'build_lifecycle.py',
})
NATIVE_TOOLING = frozenset({
    'effects.bend', 'effects.c', 'simple.h', 'simple_arena.inc.c',
    'simple_stack.inc.c', 'simple_heap.inc.c', 'simple_module.inc.c',
    'terms.inc.c', 'terms_address.inc.c', 'drop.inc.c', 'nat.inc.c',
    'text.inc.c', 'numeric.inc.c', 'f32_parse.inc.c',
})
NATIVE_TOOLS = frozenset({'build_simple.py', 'generic.mjs'})


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


COMMON = '''import Base
import ./Native.bend as Native
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Configuration.bend as C
'''

INITIALIZE = COMMON + '''import ./Protocolo.bend as P
import ./Requisitos.bend as R
import ./Seed.bend as Seed
import ./Configuracao.bend as CheckedConfiguration
import ./Environment.bend as Environment

def result(bytes: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match bytes:
    case None{}:
      [2]
    case Some{bs}:
      Con{1, bs}

def initial(ok: Bool) -> List<&2, U32>:
  match ok:
    case False{}:
      [2]
    case True{}:
      result(P.codificar(D.estado_valor(Seed.estado())))

def main() -> IO(Unit):
  Native.write(initial(CheckedConfiguration.valida(C.config(), Environment.identidade())))
'''

PREPROCESS = COMMON + '''import ./Entrada.bend as E
import ./Mensagens.bend as M

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(M.FUNCTION(E.PARSER(bytes, S.esquema(C.config()), S.limites(C.config()))))
'''

EXECUTE = COMMON + '''import ./Entrada.bend as Input
import ./Execucao.bend as E
import ./Client.bend as Client
import ./ClientProof.bend as ClientProof
import ./Bindings.bend as Bindings

def converter(i: E.Iteracao) -> Native.Iteracao<E.EstadoExecucao>:
  match i:
    case E.Continuar{s}:
      Native.Continuar{s}
    case E.Preparar{s}:
      Native.Preparar{s}
    case E.Encerrar{bs}:
      Native.Encerrar{bs}
    case E.Inconsistente{}:
      Native.Inconsistente{}

def step(estado: E.EstadoExecucao) -> Native.Iteracao<E.EstadoExecucao>:
  converter(E.avancar(estado, C.config()))

def launch(input: Input.Analise) -> IO(Unit):
  match input:
    case Input.Recebida{s, r, ctx}:
      match r:
        case P.Requisicao{credencial, codigo, argumentos, prova}:
          do IO<Unit>:
            _ : Unit <- Native.enter(1)
            Native.loop(E.EstadoExecucao, step, E.iniciar(Client.programa(), ctx, argumentos, s))
    case _:
      Native.write([2])

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    launch(Input.analisar(bytes, S.esquema(C.config()), S.limites(C.config())))
'''
# P is deliberately an explicit import, rather than inferred from another module.
EXECUTE = EXECUTE.replace('import ./Entrada.bend', 'import ./Protocolo.bend as P\nimport ./Entrada.bend')


def imports(data: bytes):
    """Header discovery for host staging; admission revalidates the full header."""
    for line in data.decode('utf-8', errors='strict').splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        if not line.startswith('import '):
            return
        m = re.fullmatch(r'import\s+(\S+)(?:\s+as\s+[A-Za-z_]\w*)?\s*(?:#.*)?', line)
        if not m:
            raise ValueError('Import inválido no ambiente do administrador')
        target = m[1]
        if target == 'Base':
            continue
        if not re.fullmatch(r'(?:\./)?(?:[A-Za-z_][\w-]*/)*[A-Za-z_][\w-]*\.bend', target):
            raise ValueError('O ambiente deve usar imports locais dentro de seu diretório')
        yield target.removeprefix('./')


class Environment:
    def __init__(self, configuration: Path, seed: Path):
        self.sources: dict[str, bytes] = {}
        self.seed_sources: dict[str, bytes] = {}
        for p in (ROOT / 'contrato').glob('*.bend'):
            self.sources[p.name] = p.read_bytes()
        for p in (ROOT / 'src').glob('*.bend'):
            if p.name in self.sources:
                raise ValueError('Colisão entre módulo próprio e contrato')
            self.sources[p.name] = p.read_bytes().replace(b'../contrato/', b'./')
        self.sources['Native.bend'] = (ROOT / 'native/effects.bend').read_bytes()
        self.foreign = (ROOT / 'native/effects.c').read_bytes()
        reserved = set(self.sources) | {'Environment.bend', 'Seed.bend', 'Main.bend',
                                      'Client.bend', 'ClientProof.bend', 'Instance.bend', 'Bindings.bend'}
        root = configuration.resolve().parent

        def load(file: Path, target: str, destination: dict[str, bytes]):
            # The registered administrator closure has no Python recursion
            # depth quota. Keep DFS order with an explicit work list; admission
            # subsequently checks the graph, including dependency cycles.
            pending = [(file,target)]
            while pending:
                file,target = pending.pop()
                file = file.resolve()
                if not file.is_relative_to(root):
                    raise ValueError('Dependência fora do diretório da configuração')
                data = file.read_bytes()
                if target in destination:
                    if destination[target] != data:
                        raise ValueError('Colisão entre dependências do administrador')
                    continue
                if target in reserved and target != 'Seed.bend':
                    raise ValueError('Administrador substituiu módulo reservado: ' + target)
                destination[target] = data
                children = []
                for imp in imports(data):
                    name = posixpath.normpath(posixpath.join(posixpath.dirname(target), imp))
                    if name in self.sources or name == 'Environment.bend':
                        continue
                    children.append((file.parent / imp,name))
                pending.extend(reversed(children))

        public: dict[str, bytes] = {}
        load(configuration, 'Configuration.bend', public)
        self.sources.update(public)
        load(seed, 'Seed.bend', self.seed_sources)
        # The environment identity covers code/tooling/public configuration only.
        # Seed and mutable data are excluded: their hash must not leak as metadata.
        paths = [p for folder in ('native', 'tools/native',
                                  'tools/admission', 'tools/verifier', 'tools/service')
                 for p in sorted((ROOT / folder).glob('*'))
                 if p.is_file() and p.suffix in ('.c', '.cc', '.h', '.S', '.cjs', '.mjs', '.py', '.json', '.bend')
                 and (folder != 'tools/service' or p.name in SERVICE_TOOLING)
                 and (folder != 'native' or p.name in NATIVE_TOOLING)
                 and (folder != 'tools/native' or p.name in NATIVE_TOOLS)]
        paths += sorted((ROOT / 'tools/admission/installed').glob('*'))
        paths += [ROOT / 'jaydb2.py', ROOT / 'tools/bootstrap.py']
        self.tooling = {str(p.relative_to(ROOT)): p.read_bytes() for p in paths}
        frontend = json.loads(self.tooling['tools/admission/frontend.lock.json'])
        frontend_manifest = self.tooling['tools/admission/installed/manifest.json']
        if json.loads(frontend_manifest) != frontend:
            raise ValueError('Manifesto do frontend instalado diverge do fixado')
        for name, expected in frontend['files'].items():
            if digest(self.tooling['tools/admission/installed/' + name]) != expected:
                raise ValueError('Artefato do frontend instalado diverge: ' + name)
        # Installation is explicit and offline. Freeze the derived verifier as
        # well as its generator/pin; a later checkout or installation edit must
        # not change the checker of an already running database.
        pin = json.loads(self.tooling['tools/verifier/verifier.lock.json'])
        installed = INSTALL_ROOT / '.tools/build' / ('verifier-' + pin['sourceSha256'])
        manifest = (installed / 'manifest.json').read_bytes()
        binary = (installed / 'bendtt-budget').read_bytes()
        if json.loads(manifest) != pin or digest(binary) != pin['kernelSha256']:
            raise ValueError('Instalação do verificador derivado diverge do manifesto fixado')
        self.tooling[VERIFIER_MANIFEST] = manifest
        self.tooling[VERIFIER_BINARY] = binary
        identity = [[k, digest(v)] for k, v in sorted(self.sources.items())]
        identity += [[name, digest(data)] for name, data in sorted(self.tooling.items())]
        self.identity = digest(json.dumps(identity, separators=(',', ':')).encode())
        self.sources['Environment.bend'] = ('import Base\ndef identidade() -> String:\n  '
                                            + json.dumps(self.identity) + '\n').encode()
        # Every value is immutable bytes; no later staging operation needs to
        # edit these tables. Work on fresh dictionaries for each entry module.
        self.sources = MappingProxyType(self.sources)
        self.seed_sources = MappingProxyType(self.seed_sources)
        self.tooling = MappingProxyType(self.tooling)

    def materialize_tooling(self, directory: Path):
        # Compilation after startup reads the very bytes in the environment's
        # identity, including frontend adapters and native runtime snippets.
        # A later edit in the developer checkout cannot change a live instance.
        directory.mkdir(mode=0o700)
        for name, data in self.tooling.items():
            path = directory / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            if name == VERIFIER_BINARY:
                path.chmod(0o700)
        return directory

    def stage(self, directory: Path, purpose: str, metadata=None):
        available = dict(self.sources)
        if purpose == 'initialize':
            available.update(self.seed_sources)
            main = INITIALIZE
        elif purpose in ('decode', 'authenticate'):
            main = PREPROCESS.replace('FUNCTION', 'enquadramento' if purpose == 'decode' else 'autenticacao')
            main = main.replace('PARSER', 'decodificar' if purpose == 'decode' else 'analisar')
        elif purpose == 'execute':
            for name, data in zip(('Client.bend', 'ClientProof.bend', 'Instance.bend', 'Bindings.bend'), metadata, strict=True):
                available[name] = data
            main = EXECUTE
        else:
            raise ValueError('Finalidade inválida')
        available['Main.bend'] = main.encode()
        selected = {}

        def select(name):
            pending = [name]
            while pending:
                name = pending.pop()
                if name in selected:
                    continue
                if name not in available:
                    raise ValueError('Dependência não admitida: ' + name)
                selected[name] = available[name]
                children = [posixpath.normpath(posixpath.join(posixpath.dirname(name), target))
                            for target in imports(available[name])]
                pending.extend(reversed(children))

        select('Main.bend')
        # These exact target modules are mandatory even if erased by compilation.
        if purpose == 'execute':
            select('Interface.bend')
        manifest = {'submissionDir': str(directory.resolve()), 'entry': 'Main.bend', 'dependencies': []}
        for name, data in selected.items():
            path = directory / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            role = 'library'
            exports = []
            if name == 'Native.bend':
                role = 'kernel'
            elif name in ('Client.bend', 'ClientProof.bend'):
                role = 'client'
            elif name in ('Main.bend', 'Seed.bend') or name in self.seed_sources:
                role = 'host'
            elif name in ('Environment.bend', 'Instance.bend', 'Bindings.bend'):
                role = 'host'
                exports = {'Environment.bend': ['Environment:identidade'],
                    'Instance.bend': ['Instance:config', 'Instance:contexto', 'Instance:argumentos'],
                    'Bindings.bend': ['Bindings:codigo', 'Bindings:certificado', 'Bindings:termina']}[name]
            elif name == 'Configuration.bend' and purpose == 'initialize':
                role = 'host'
            dep = {'path': name, 'role': role, 'sha256': digest(data)}
            if role == 'host':
                dep['exports'] = exports
            manifest['dependencies'].append(dep)
        (directory / 'effects.c').write_bytes(self.foreign)
        primitives = ['read', 'write', 'enter', 'loop']
        manifest['kernel'] = {'module': 'Native.bend', 'primitives': primitives,
            'foreign': {'path': 'effects.c', 'sha256': digest(self.foreign)}, 'loopStep': 'step'}
        if purpose != 'execute':
            # Keep only the ABI actually used by the entry, so there is no loopStep.
            data = available['Native.bend'].split(b'\ntype Iteracao', 1)[0]
            # Primitive functions precede Iteracao in effects.bend.
            (directory / 'Native.bend').write_bytes(data)
            for dep in manifest['dependencies']:
                if dep['path'] == 'Native.bend':
                    dep['sha256'] = digest(data)
            manifest['kernel']['primitives'] = ['read', 'write', 'enter']
            del manifest['kernel']['loopStep']
            manifest['purpose'] = 'initialize' if purpose == 'initialize' else 'preprocess'
        else:
            manifest['openTargets'] = {'Bindings:certificado': 'ClientProof.bend', 'Bindings:termina': 'ClientProof.bend'}
        if purpose == 'initialize':
            manifest['initialization'] = {'configuration': 'Configuration:config', 'state': 'Seed:estado', 'proof': 'Seed:inicial_valido'}
        (directory / 'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False))
        return manifest
