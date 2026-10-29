import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { admitSubmission, admitKernel, buildKernel, emitC, emitGenericC, bootstrapInfo, AdmissionError } from '../../tools/admission/index.mjs';
import { sha256 } from '../../tools/admission/bootstrap.mjs';
import { fixture, repo } from './helpers.mjs';

const backendSha256 = sha256(fs.readFileSync(path.join(repo, 'tools/native/generic.mjs')));
const primitives = `import Base

type Iteracao<-A: Type> is Type:
  Continuar{estado: A}
  Preparar{estado: A}
  Encerrar{bytes: List<&2, U32>}
  Inconsistente{}

def read() -> IO(List<&2, U32>):
  import "./effects.c"

def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"

def enter(etapa: U32) -> IO(Unit):
  import "./effects.c"

def loop(-A: Type, step: A -> Iteracao<A>, initial: A) -> IO(Unit):
  import "./effects.c"
`;
const finiteMain = `import Base
import ./Native.bend as Native

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(bytes)
`;

function nativeFixture(t, { kernelOnly = false, loop = false } = {}) {
  const f = fixture(t);
  f.write('Native.bend', loop ? primitives : primitives.slice(0, primitives.indexOf('\ndef loop(')), 'kernel');
  f.write('effects.c', fs.readFileSync(path.join(repo, 'native/effects.c'), 'utf8'));
  f.write('Main.bend', (kernelOnly ? '' : 'import ./ClientProof.bend as Proof\n') + finiteMain);
  if (kernelOnly) for (const [file, role] of f.roles) if (role === 'client' || ['Bindings.bend', 'Instance.bend'].includes(file)) f.roles.delete(file);
  const manifest = () => {
    const m = f.manifest();
    m.kernel = { module: 'Native.bend', primitives: loop ? ['read', 'write', 'enter', 'loop'] : ['read', 'write', 'enter'],
      ...(loop ? { loopStep: 'step' } : {}),
      foreign: { path: 'effects.c', sha256: sha256(f.read('effects.c')) } };
    if (kernelOnly) { delete m.openTargets; m.purpose = 'preprocess'; }
    return m;
  };
  return { ...f, manifest };
}

async function rejected(call, codes) {
  await assert.rejects(call, e => e instanceof AdmissionError && (assert.ok(codes.includes(e.code), `${e.code}: ${e.message}`), true));
}

function runNative(f, emission, mode = 'finite') {
  const source = path.join(f.root, 'checked.c');
  fs.writeFileSync(source, emission.c);
  const run = child.spawnSync('/usr/bin/python3', ['-B', path.join(repo, 'tests/admission/runtime_probe.py'), source, path.join(f.root, 'module.so'), mode],
    { encoding: 'utf8', timeout: 60000 });
  assert.equal(run.status, 0, run.stderr);
  return JSON.parse(run.stdout);
}

test('kernel IO com cliente puro: dois checkers reais e C genérico do mesmo Book', async t => {
  const f = nativeFixture(t);
  const calls = [], spawn = child.spawnSync;
  child.spawnSync = function (bin, args, options) {
    if (bin === bootstrapInfo().verifier.kernelPath) calls.push(fs.readFileSync(args[0], 'utf8'));
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  let admitted;
  try { admitted = await admitSubmission(f.manifest()); }
  finally { child.spawnSync = spawn; syncBuiltinESMExports(); }
  const book = admitted.book;
  assert.equal(calls.length, 1);
  assert.ok(/^main :/m.test(calls[0]));
  assert.match(calls[0], /certificado/);
  assert.equal(book.tlds['Native:read'].b, true);
  assert.equal(book.tlds.main.b, undefined);
  assert.ok(book.tlds.main.e);
  f.write('effects.c', '#error original foreign source must not be reloaded');
  f.write('Main.bend', 'invalid after admission');
  const emission = await emitGenericC(admitted, { backendSha256 });
  assert.strictEqual(book, admitted.book);
  assert.equal(emission.sameCheckedBook, true);
  assert.match(emission.c, /^\/\/ JAYDB_NATIVE_GENERIC_V1 [a-f0-9]{64}\n/);
  assert.equal(emission.cSha256, sha256(emission.c));
  assert.strictEqual(await emitGenericC(admitted, { backendSha256 }), emission);
  assert.throws(() => emitC(admitted), { code: 'BACKEND_CHANGED' });
  assert.deepEqual(runNative(f, emission), { status: 0, output: [0, 255, 128, 65] });
});

test('admitKernel/buildKernel não exigem Client ou Bindings fictícios', async t => {
  const f = nativeFixture(t, { kernelOnly: true });
  const { admitted, emission } = await buildKernel(f.manifest(), { backendSha256 });
  assert.equal(admitted.report.purpose, 'preprocess');
  assert.equal(admitted.report.clientClosureSize, 0);
  assert.deepEqual(admitted.report.targets, []);
  assert.equal(admitted.book.tlds['Bindings:certificado'], undefined);
  assert.match(emission.c, /CID_Native_read/);
  assert.match(emission.c, /CID_Native_write/);
});

test('loop genérico é primitiva IO; step e main passam pelos dois checkers', async t => {
  const f = nativeFixture(t, { kernelOnly: true, loop: true });
  f.write('Main.bend', `import Base
import ./Native.bend as Native

type EstadoExecucao is Type:
  EstadoExecucao{restante: Nat}

def step(estado: EstadoExecucao) -> Native.Iteracao<EstadoExecucao>:
  match estado:
    case EstadoExecucao{n}:
      match n:
        case 0n:
          Native.Encerrar{[65]}
        case 1n+m:
          match m:
            case 0n:
              Native.Preparar{EstadoExecucao{0n}}
            case 1n+k:
              Native.Continuar{EstadoExecucao{m}}

def main() -> IO(Unit):
  do IO<Unit>:
    _ : Unit <- Native.enter(1)
    Native.loop(EstadoExecucao, step, EstadoExecucao{3n})
`);
  const a = await admitKernel(f.manifest());
  assert.equal(a.book.tlds['Native:loop'].b, true);
  assert.ok(a.book.tlds.step.e);
  assert.equal(a.book.tlds.step.b, undefined);
  assert.equal(a.book.tlds['Native:Iteracao'].b, undefined);
  const emission = await emitGenericC(a, { backendSha256 });
  assert.match(emission.c, /CID_Native_loop/);
  assert.deepEqual(runNative(f, emission, 'loop'), { status: 0, output: [65], stage: 2 });
});

for (const [name, body] of [
  ['direto', 'def hidden() -> IO(Unit):\n  N.write([1])\n'],
  ['tipo', 'type Hidden is Type:\n  Hidden{io: IO(Unit)}\n'],
  ['construtor kernel', 'def hidden() -> N.Iteracao<Unit>:\n  N.Encerrar{[1]}\n'],
  ['lambda apagada', 'def hidden() -> Unit:\n  (x => Unit{})(u => N.write([1]))\n'],
  ['termo apagado', 'def hidden() -> Unit:\n  (x => Unit{})(N.read())\n'],
  ['template sem instanciar', 'def hidden(~f: Unit -> IO(Unit), u: Unit) -> IO(Unit):\n  f(u)\n'],
]) {
  test(`cliente continua sem acesso à ABI: ${name}`, async t => {
    const f = nativeFixture(t);
    f.write('Client.bend', 'import ./Native.bend as N\n' + f.read('Client.bend') + '\n' + body);
    f.bindCode();
    await rejected(admitSubmission(f.manifest()), ['IO', 'KERNEL_CAPTURE']);
  });
}

test('cadeia de exports host não pode esconder IO ou kernel', async t => {
  const f = nativeFixture(t);
  f.write('Bridge.bend', 'import Base\nimport ./Native.bend as N\ndef get() -> IO(Unit):\n  N.write([1])\n', 'host');
  f.write('Client.bend', 'import ./Bridge.bend as Bridge\n' + f.read('Client.bend') + '\ndef hidden() -> Unit:\n  (x => Unit{})(Bridge.get())\n');
  f.bindCode();
  const m = f.manifest();
  m.dependencies.find(d => d.path === 'Bridge.bend').exports = ['Bridge:get'];
  await rejected(admitSubmission(m), ['IO', 'KERNEL_CAPTURE']);
});

for (const [name, transform, codes] of [
  ['foreign não listado', s => s + '\ndef extra() -> IO(Unit):\n  import "./effects.c"\n', ['FOREIGN']],
  ['novo axioma', s => s + '\nlaw invented:\n  Empty\n', ['OPEN_LAW']],
  ['unsafe', s => s + '\ndef bad?(x: Unit) -> Unit:\n  x\n', ['UNSAFE']],
  ['meta', s => s + '\ndef bad() -> Unit:\n  ?hole\n', ['META']],
  ['corpo não checado', s => s + '\ndef bad() -> Unit:\n  123\n', ['PRIMARY_CHECK']],
  ['assinatura ABI substituída', s => s.replace('def read() -> IO(List<&2, U32>)', 'def read() -> IO(Unit)'), ['KERNEL_ABI']],
  ['foreign alternativo', s => s.replace('import "./effects.c"', 'import "./other.c"'), ['KERNEL_ABI']],
  ['IO Base além da ABI', s => s + '\ndef extra() -> IO(Unit):\n  IO.print("forbidden")\n', ['IO']],
]) {
  test(`role kernel não permite ${name}`, async t => {
    const f = nativeFixture(t, { kernelOnly: true });
    f.write('Native.bend', transform(f.read('Native.bend')));
    await rejected(admitKernel(f.manifest()), codes);
  });
}

test('kernel hash, snapshot C, symlink e pin de backend continuam obrigatórios', async t => {
  const f = nativeFixture(t, { kernelOnly: true });
  const original = f.manifest();
  f.write('Native.bend', f.read('Native.bend') + '\n');
  await rejected(admitKernel(original), ['HASH']);
  const c = f.manifest();
  f.write('effects.c', f.read('effects.c') + '\n');
  await rejected(admitKernel(c), ['HASH']);
  const a = await admitKernel(f.manifest());
  await rejected(emitGenericC(a, { backendSha256: '0'.repeat(64) }), ['BACKEND']);
  const b = await admitKernel(f.manifest());
  await rejected(emitGenericC(b, { backendSha256, compiler: () => 'bad' }), ['BACKEND']);
  const m = f.manifest();
  fs.renameSync(path.join(f.root, 'effects.c'), path.join(f.root, 'original.c'));
  fs.symlinkSync('original.c', path.join(f.root, 'effects.c'));
  await rejected(admitKernel(m), ['PATH']);
});

function initialFixture(t) {
  const f = nativeFixture(t, { kernelOnly: true });
  f.write('Configuration.bend', f.read('Instance.bend'), 'host');
  f.write('Seed.bend', `import Base
import ./Dados.bend as D
import ./Logica.bend as L
import ./Requisitos.bend as R
import ./Configuration.bend as C

def estado() -> D.Estado:
  D.Estado{Nil{}, Nil{}}

law valido:
  R.Valido(C.config(), estado())

def valido():
  L.Ambos{{==}, L.Ambos{Unit{}, Unit{}}}
`, 'host');
  return { ...f, manifest() { return { ...f.manifest(), purpose: 'initialize', initialization: {
    configuration: 'Configuration:config', state: 'Seed:estado', proof: 'Seed:valido' } }; } };
}

test('inicialização verifica Valido real com lei não vazia, sem programa fictício', async t => {
  const f = initialFixture(t);
  const a = await admitKernel(f.manifest());
  assert.equal(a.report.purpose, 'initialize');
  assert.ok(a.book.tlds['Seed:valido'].e);
  assert.equal(a.book.tlds['Seed:valido'].b, undefined);
  assert.equal(a.report.initialization.proof, 'Seed:valido');
});

test('Safe traduz tamanhos lógicos grandes sem overflow de stack, preservando prova e Book', async t => {
  const f = initialFixture(t);
  f.write('Configuration.bend', f.read('Configuration.bend').replace(
    'S.Limites{256n, 256n, 256n}',
    'S.Limites{32768n, 65536n, 32768n}'));
  const a = await admitKernel(f.manifest());
  assert.equal(a.report.bendtt, true);
  assert.match(a.report.safeNumeralsSha256, /^[a-f0-9]{64}$/);
  assert.match(a.sources.find(s => s.path === 'Configuration.bend').text, /S\.Limites\{32768n, 65536n, 32768n\}/);
  assert.ok(a.book.tlds['Seed:valido'].e);
  assert.ok((await emitGenericC(a, { backendSha256 })).c.length > 1000);
  f.write('Configuration.bend', f.read('Configuration.bend').replace('case S.Estavel{s}:\n      Unit', 'case S.Estavel{s}:\n      Empty'));
  await rejected(admitKernel(f.manifest()), ['PRIMARY_CHECK']);
});

test('inicialização rejeita prova enfraquecida, falsa, aberta ou para outro estado/config', async t => {
  for (const [from, to, codes] of [
    ['R.Valido(C.config(), estado())', 'Unit', ['INITIALIZATION']],
    ['L.Ambos{{==}, L.Ambos{Unit{}, Unit{}}}', 'Unit{}', ['PRIMARY_CHECK']],
    ['def valido():\n  L.Ambos{{==}, L.Ambos{Unit{}, Unit{}}}', '', ['INITIALIZATION']],
    ['R.Valido(C.config(), estado())', 'R.Valido(C.config(), D.Estado{Nil{}, Nil{}})', ['INITIALIZATION']],
  ]) {
    const f = initialFixture(t);
    f.write('Seed.bend', f.read('Seed.bend').replace(from, to));
    await rejected(admitKernel(f.manifest()), codes);
  }
  const f = initialFixture(t);
  const m = f.manifest();
  delete m.initialization;
  await rejected(admitKernel(m), ['INITIALIZATION']);
});

test('sem clientes, também não aceita bypass por role client ou openTargets', async t => {
  const f = nativeFixture(t);
  const m = f.manifest();
  m.purpose = 'preprocess';
  delete m.openTargets;
  await rejected(admitKernel(m), ['MANIFEST']);
});

test('contrato/ byte-idêntico e nomes canônicos configuráveis, sem symlinks', async t => {
  const f = fixture(t), original = f.manifest();
  const renamed = new Map(original.dependencies.map(d => [d.path, d.role === 'library' ? 'contrato/' + d.path : ({
    'Client.bend': 'customer/Program.bend', 'ClientProof.bend': 'customer/Proof.bend',
    'Instance.bend': 'generated/Inst.bend', 'Bindings.bend': 'generated/Bind.bend',
  }[d.path] ?? d.path)]));
  const copies = new Map();
  for (const dep of original.dependencies) {
    const dest = renamed.get(dep.path);
    let source = f.read(dep.path);
    if (dep.role !== 'library') source = source.replace(/^import (\.\/\w+\.bend) as /gm, (line, spec) => {
      let relative = path.posix.relative(path.posix.dirname(dest), renamed.get(spec.slice(2)));
      if (!relative.startsWith('.')) relative = './' + relative;
      return line.replace(spec, relative);
    });
    copies.set(dest, source);
  }
  const bind = copies.get('generated/Bind.bend'), beg = bind.indexOf('def codigo()'), end = bind.indexOf('\nlaw certificado:', beg);
  copies.set('generated/Bind.bend', bind.slice(0, beg) + 'def codigo() -> String:\n  ' + JSON.stringify(copies.get('customer/Program.bend')) + '\n' + bind.slice(end));
  for (const [file, source] of copies) f.write(file, source);
  const canonicalRefs = { contractPrefix: 'contrato/', bindings: 'generated/Bind.bend', instance: 'generated/Inst.bend', client: 'customer/Program.bend' };
  const exports = { 'generated/Bind.bend': ['generated/Bind:codigo', 'generated/Bind:certificado', 'generated/Bind:termina'],
    'generated/Inst.bend': ['generated/Inst:config', 'generated/Inst:contexto', 'generated/Inst:argumentos', 'generated/Inst:NaoObserva'] };
  const m = { ...original, canonicalRefs,
    dependencies: original.dependencies.map(d => ({ ...d, path: renamed.get(d.path), sha256: sha256(copies.get(renamed.get(d.path))),
      ...(d.role === 'host' ? { exports: exports[renamed.get(d.path)] ?? [] } : {}) })),
    openTargets: { 'generated/Bind:certificado': 'customer/Proof.bend', 'generated/Bind:termina': 'customer/Proof.bend' } };
  const a = await admitSubmission(m);
  assert.ok(a.book.tlds['contrato/Requisitos:Certifica']);
  assert.ok(a.book.tlds['generated/Bind:certificado'].e);
  for (const dep of original.dependencies.filter(d => d.role === 'library')) {
    assert.equal(a.sources.find(s => s.path === 'contrato/' + dep.path).sha256, dep.sha256);
  }
  await rejected(admitSubmission({ ...m, canonicalRefs: { ...canonicalRefs, contractPrefix: '' } }), ['CONTRACT']);
  await rejected(admitSubmission({ ...m, canonicalRefs: { ...canonicalRefs, contractPrefix: 'other/' } }), ['MANIFEST']);
  f.write('contrato/Dados.bend', copies.get('contrato/Dados.bend') + '\n');
  const wrong = { ...m, dependencies: m.dependencies.map(d => d.path === 'contrato/Dados.bend' ? { ...d, sha256: sha256(f.read(d.path)) } : d) };
  await rejected(admitSubmission(wrong), ['CONTRACT']);
});

test('pré-processamento carrega src puro original e contrato/ intacto no mesmo Book', async t => {
  const f = nativeFixture(t, { kernelOnly: true });
  for (const [file, role] of [...f.roles]) if (role === 'library') {
    f.write('contrato/' + file, f.read(file), 'library');
    f.roles.delete(file);
  }
  for (const name of ['Codec', 'Entrada', 'Estado', 'Gerar', 'Nucleo', 'Reificacao', 'Requisicao', 'Transporte']) {
    f.write('src/' + name + '.bend', fs.readFileSync(path.join(repo, 'src', name + '.bend'), 'utf8'), 'host');
  }
  const a = await admitKernel({ ...f.manifest(), canonicalRefs: { contractPrefix: 'contrato/' } });
  assert.ok(a.book.tlds['src/Nucleo:fidelidade_de_todos_os_prefixos'].e);
  assert.ok(a.book.tlds['src/Nucleo:certificado_cobre_maquina_incremental'].e);
  assert.equal(a.report.bendtt, true);
});

test('administrador pode fornecer preenchimento explícito da prova inicial em outro arquivo', async t => {
  const f = initialFixture(t);
  const source = f.read('Seed.bend'), split = source.indexOf('\ndef valido():');
  f.write('Seed.bend', source.slice(0, split));
  f.write('SeedProof.bend', 'import Base\nimport ./Seed.bend as Seed\nimport ./Logica.bend as L\n' + source.slice(split).replace('def valido()', 'def Seed.valido()'), 'host');
  const m = f.manifest();
  m.initialization.proofFile = 'SeedProof.bend';
  const a = await admitKernel(m);
  assert.ok(a.book.tlds['Seed:valido'].e);
  delete m.initialization.proofFile;
  await rejected(admitKernel(m), ['REDEFINITION']);
});

test('Book genérico continua selado antes, durante e após emissão', async t => {
  const f = nativeFixture(t, { kernelOnly: true });
  const a = await admitKernel(f.manifest());
  const pending = emitGenericC(a, { backendSha256 });
  a.book.tlds.main.u = true;
  await rejected(pending, ['BOOK_CHANGED']);
  const b = await admitKernel(f.manifest());
  const emitted = await emitGenericC(b, { backendSha256 });
  assert.throws(() => { b.book.tlds['Native:read'].b = false; }, TypeError);
  assert.throws(() => { b.book.tlds.unchecked = b.book.tlds.main; }, /verification/);
  assert.equal(await emitGenericC(b, { backendSha256 }), emitted);
  await rejected(emitGenericC({ book: b.book }, { backendSha256 }), ['BOOK_CHANGED']);
});

test('ABI recusa união2 legada e passos capturados/aliases ou escolhidos pelo cliente', async t => {
  for (const mode of ['legacy', 'capture', 'alias', 'client']) {
    const f = nativeFixture(t, { loop: true });
    f.write('Main.bend', `import Base
import ./Native.bend as N
import ./ClientProof.bend as Proof
import ./Client.bend as Client
def step(u: Unit) -> N.Iteracao<Unit>:
  N.Encerrar{[65]}
def main() -> IO(Unit):
  N.loop(Unit, ${mode === 'capture' ? 'u => step(u)' : 'step'}, Unit{})
`);
    const m = f.manifest();
    if (mode === 'legacy') f.write('Native.bend', f.read('Native.bend').replace('  Preparar{estado: A}\n', '').replace('  Inconsistente{}\n', ''));
    if (mode === 'alias') f.write('Main.bend', f.read('Main.bend') + '\ndef alias() -> @-A: Type -> (A -> N.Iteracao<A>) -> A -> IO(Unit):\n  N.loop\n');
    if (mode === 'client') m.kernel.loopStep = 'Client:programa';
    const fresh = f.manifest();
    fresh.kernel.loopStep = m.kernel.loopStep;
    await rejected(admitSubmission(fresh), ['KERNEL_ABI']);
  }
});

test('enter admite helpers da entrada e rejeita reset, alias e helper de outro módulo', async t => {
  const f = nativeFixture(t, { kernelOnly: true });
  f.write('Main.bend', `import Base
import ./Native.bend as N
def launch() -> IO(Unit):
  do IO<Unit>:
    _ : Unit <- N.enter(1)
    N.write([65])
def main() -> IO(Unit):
  launch()
`);
  assert.equal((await admitKernel(f.manifest())).report.bendtt, true);
  f.write('Main.bend', f.read('Main.bend').replace('N.enter(1)', 'N.enter(0)'));
  await rejected(admitKernel(f.manifest()), ['KERNEL_ABI']);
  f.write('Main.bend', finiteMain);
  f.write('Native.bend', f.read('Native.bend') + '\ndef hidden() -> IO(Unit):\n  enter(1)\n');
  await rejected(admitKernel(f.manifest()), ['KERNEL_ABI']);
});

test('CLI admite kernel e emite backend genérico com pin explícito', t => {
  const f = nativeFixture(t, { kernelOnly: true });
  const file = path.join(f.root, 'host.json'), c = path.join(f.root, 'out.c');
  fs.writeFileSync(file, JSON.stringify(f.manifest()));
  const run = child.spawnSync(process.execPath, [path.join(repo, 'tools/admission/cli.mjs'), '--manifest', file,
    '--emit-c', c, '--generic-backend-sha256', backendSha256], { encoding: 'utf8', timeout: 30000 });
  assert.equal(run.status, 0, run.stderr);
  assert.equal(JSON.parse(run.stdout).purpose, 'preprocess');
  assert.match(fs.readFileSync(c, 'utf8'), /^\/\/ JAYDB_NATIVE_GENERIC_V1 /);
});

test('staging real do serviço: inicialização, decode e autenticação com configuração do exemplo', async t => {
  const f = fixture(t);
  const script = `from pathlib import Path
import sys
from tools.service.staging import Environment
root = Path(sys.argv[1])
env = Environment(Path('examples/sem-observacoes/Configuration.bend'), Path('examples/sem-observacoes/Seed.bend'))
for purpose in ('initialize', 'decode', 'authenticate'):
    env.stage(root / purpose, purpose)
`;
  const staged = child.spawnSync('/usr/bin/python3', ['-B', '-c', script, f.root], { cwd: repo, encoding: 'utf8', timeout: 10000 });
  assert.equal(staged.status, 0, staged.stderr);
  for (const purpose of ['initialize', 'decode', 'authenticate']) {
    const m = JSON.parse(fs.readFileSync(path.join(f.root, purpose, 'manifest.json'), 'utf8'));
    const a = await admitKernel(m);
    assert.equal(a.report.primary, true);
    assert.equal(a.report.bendtt, true);
    assert.ok((await emitGenericC(a, { backendSha256 })).c.length > 100000);
  }
});
