import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { admitSubmission, emitC, preflight, AdmissionError, bootstrapInfo } from '../../tools/admission/index.mjs';
import { fixture, repo } from './helpers.mjs';

const rejection = async (manifest, codes) => {
  await assert.rejects(admitSubmission(manifest), e => {
    assert.ok(e instanceof AdmissionError);
    assert.ok(codes.includes(e.code), `${e.code}: ${e.message}`);
    return true;
  });
};

test('programa recursivo, lei não vazia, dois checkers reais, C do Book e CPU', async t => {
  const f = fixture(t);
  const exactSource = f.read('Client.bend');
  assert.match(f.read('Instance.bend'), /MaisUmaLei\{NaoObserva/);
  const savedSpawn = child.spawnSync;
  const calls = [];
  child.spawnSync = function (bin, args, options) {
    if (bin === bootstrapInfo().verifier.kernelPath) calls.push({ bin, text: fs.readFileSync(args[0], 'utf8') });
    return savedSpawn(bin, args, options);
  };
  syncBuiltinESMExports();
  let admitted;
  try { admitted = await admitSubmission(f.manifest()); }
  finally { child.spawnSync = savedSpawn; syncBuiltinESMExports(); }
  assert.equal(calls.length, 1);
  assert.match(calls[0].text, /certificado/);
  assert.match(calls[0].text, /termina/);
  assert.equal(admitted.report.primary, true);
  assert.equal(admitted.report.bendtt, true);
  assert.ok(admitted.book.tlds['Bindings:certificado'].e);
  // Changing every on-disk source after checking cannot change emitted C.
  fs.writeFileSync(path.join(f.root, 'Client.bend'), 'invalid after admission');
  const c = emitC(admitted);
  assert.equal(emitC(admitted), c);
  fs.writeFileSync(path.join(f.root, 'program.c'), c);
  const build = child.spawnSync('/usr/bin/clang-19', ['-O1', '-w', '-x', 'c', 'program.c', '-o', 'program', '-lm', '-pthread'], { cwd: f.root, encoding: 'utf8', timeout: 60000 });
  assert.equal(build.status, 0, build.stderr);
  const run = child.spawnSync(path.join(f.root, 'program'), [], { encoding: 'utf8', timeout: 10000 });
  assert.equal(run.status, 0, run.stderr);
  assert.equal(run.stdout.trim(), 'Dados.VInt{0, 6}');
  assert.equal(admitted.sources.find(s => s.path === 'Client.bend').text, exactSource);
});

test('prova anterior falha quando novo programa observa dados', async t => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend').replace('S.Recusar{D.VInt{0, contar([1, 2, 3], 0)}}', 'S.Acessar{D.ContarLinhas{D.Usuarios{}}, r => S.Recusar{D.VInt{0, 6}}}'));
  f.bindCode();
  await rejection(f.manifest(), ['PRIMARY_CHECK']);
});

test('preserva fontes exatas, CRLF, Unicode, comentários e strings com palavras de efeitos', async t => {
  const f = fixture(t);
  const source = (f.read('Client.bend') + '\n# IO foreign @unsafe ?axioma import 0xdeadbeef/x.bend\ndef IO_print() -> String:\n  "ação 漢字 😀 IO.print @unsafe ?meta"\n').replaceAll('\n', '\r\n');
  f.write('Client.bend', source);
  f.bindCode();
  const got = await admitSubmission(f.manifest());
  assert.equal(got.sources.find(s => s.path === 'Client.bend').text, source);
  assert.equal(got.sources.find(s => s.path === 'Client.bend').bytes, Buffer.byteLength(source));
  assert.equal(got.book.tlds['Bindings:codigo'].v.v, source);
});

test('preserva tipos, templates, higher order, funções e leis puras preenchidas', async t => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend') + `
type Caixa is Data:
  Caixa{valor: U32}

def aplicar(~f: U32 -> U32, x: U32) -> U32:
  f(x)

def identidade(x: U32) -> U32:
  x

def higher(f: U32 -> U32, x: U32) -> U32:
  f(x)

def extra() -> Caixa:
  Caixa{higher(identidade, aplicar(identidade, 6))}

law identidade_certa:
  {identidade(6) == 6 : U32}

def identidade_certa():
  {==}
`);
  f.bindCode();
  const a = await admitSubmission(f.manifest());
  assert.ok(a.book.tmps['Client:aplicar'].size);
});

const attacks = [
  ['IO não usado', 'def hidden() -> IO(Unit):\n  IO.print("efeito")\n', ['IO']],
  ['IO escondido em tipo', 'type CaixaIO is Type:\n  CaixaIO{f: IO(Unit)}\n', ['IO']],
  ['IO encapsulado em lambda', 'def hidden() -> Unit -> IO(Unit):\n  u => IO.exit(0)\n', ['IO']],
  ['IO descartado por beta redução', 'def hidden() -> Unit:\n  (x => Unit{})(IO.print("efeito"))\n', ['IO']],
  ['foreign C/JS', 'def hidden() -> IO(Unit):\n  import "./malicious.c"\n  import "./malicious.js"\n', ['FOREIGN']],
  ['unsafe decorator', '@unsafe\ndef hidden(n: Nat) -> Nat:\n  hidden(n)\n', ['UNSAFE']],
  ['unsafe abreviação ?', 'def hidden?(n: Nat) -> Nat:\n  hidden(n)\n', ['UNSAFE']],
  ['meta explícita', 'def hidden() -> Unit:\n  ?todo\n', ['META']],
  ['meta descartada por beta redução', 'def hidden() -> Unit:\n  (x => Unit{})(?todo)\n', ['META']],
  ['IO em braço de match descartado', 'def hidden(n: Nat) -> Unit:\n  match n:\n    case _:\n      Unit{}\n    case 0n:\n      (x => Unit{})(IO.exit(0))\n', ['IO']],
  ['axioma aberto', 'law invented:\n  Empty\n', ['OPEN_LAW']],
  ['lei aberta em tipo', 'law invented:\n  Type\n', ['OPEN_LAW']],
  ['tipo Base redefinido', 'type U32 is Data:\n  Fake{}\n', ['PARSE']],
  ['tipo do contrato redefinido', 'type D.Valor is Data:\n  Fake{}\n', ['PARSE']],
];
for (const [name, body, codes] of attacks) {
  test(`rejeita ${name} inclusive fora do caminho executado`, async t => {
    const f = fixture(t);
    const marker = path.join(f.root, 'effect-ran');
    f.write('malicious.c', '#error foreign source must never be read');
    f.write('malicious.js', `require('node:fs').writeFileSync(${JSON.stringify(marker)}, 'BAD')`);
    f.write('Client.bend', f.read('Client.bend') + '\n' + body);
    f.bindCode();
    await rejection(f.manifest(), codes);
    assert.equal(fs.existsSync(marker), false);
  });
}

for (const spec of ['0xdeadbeef/x.bend', 'package@1.0.0.0/x.bend', 'https://example.com/x.bend', '/tmp/x.bend']) {
  test(`preflight rejeita ${spec} antes de carregar frontend`, async t => {
    const f = fixture(t);
    f.write('Unreachable.bend', `import ${spec} as Remote\n`, 'client');
    const manifest = f.manifest();
    manifest.toolchain = { sourceDir: '/nonexistent/frontend' };
    const saved = globalThis.fetch;
    let fetches = 0;
    globalThis.fetch = () => { fetches++; throw new Error('unexpected fetch'); };
    try { await rejection(manifest, ['IMPORT']); }
    finally { globalThis.fetch = saved; }
    assert.equal(fetches, 0);
  });
}

test('resolve imports transitivos com aliases e caminhos locais relativos', async t => {
  const f = fixture(t);
  f.write('lib/Value.bend', 'import Base\ndef numero() -> U32:\n  6\n', 'library');
  f.write('lib/Helper.bend', 'import Base\nimport ./Value.bend as Different\ndef numero() -> U32:\n  Different.numero()\n', 'library');
  f.write('Client.bend', f.read('Client.bend').replace('import Base', 'import Base\nimport ./lib/Helper.bend as Renamed') + '\ndef mais() -> U32:\n  Renamed.numero()\n');
  f.bindCode();
  const a = await admitSubmission(f.manifest());
  assert.ok(a.book.tlds['lib/Helper:numero']);
  assert.ok(a.book.tlds['lib/Value:numero']);
});

test('rejeita efeito em dependência transitiva admitida e apelidada', async t => {
  const f = fixture(t);
  f.write('lib/Leaf.bend', 'import Base\ndef valor() -> IO(Unit):\n  IO.exit(0)\n', 'library');
  f.write('lib/Bridge.bend', 'import Base\nimport ./Leaf.bend as Alias\ndef valor() -> IO(Unit):\n  Alias.valor()\n', 'library');
  f.write('Client.bend', 'import ./lib/Bridge.bend as Other\n' + f.read('Client.bend'));
  f.bindCode();
  await rejection(f.manifest(), ['IO']);
});

test('biblioteca local existente precisa estar no conjunto explícito', async t => {
  const f = fixture(t);
  f.write('Unfixed.bend', 'import Base\ndef n() -> U32:\n  6\n');
  f.write('Client.bend', 'import ./Unfixed.bend as X\n' + f.read('Client.bend'));
  f.bindCode();
  await rejection(f.manifest(), ['DEPENDENCY']);
});

test('preflight verifica ciclo, alias repetido e escape do diretório', async t => {
  for (const kind of ['cycle', 'alias', 'escape']) {
    const f = fixture(t);
    const imports = { cycle: 'import ./Client.bend as Me\n', alias: 'import ./Dados.bend as D\n', escape: 'import ../Outside.bend as X\n' };
    f.write('Client.bend', imports[kind] + f.read('Client.bend'));
    f.bindCode();
    await rejection(f.manifest(), [kind === 'cycle' ? 'IMPORT_CYCLE' : kind === 'alias' ? 'IMPORT' : 'DEPENDENCY']);
  }
});

test('nega preenchimento de lei de biblioteca, mesmo explicitamente importada', async t => {
  const f = fixture(t);
  f.write('Policy.bend', 'import Base\nlaw aberta:\n  Unit\n', 'library');
  f.write('Client.bend', 'import ./Policy.bend as P\n' + f.read('Client.bend') + '\ndef P.aberta():\n  Unit{}\n');
  f.bindCode();
  await rejection(f.manifest(), ['REDEFINITION']);
});

for (const body of [
  'def I.config() -> Unit:\n  Unit{}\n',
  'def I.contexto() -> Unit:\n  Unit{}\n',
  'def I.argumentos() -> Unit:\n  Unit{}\n',
  'def I.NaoObserva(h: S.Situacao) -> Type:\n  Unit\n',
  'def B.codigo() -> String:\n  "falso"\n',
]) {
  test(`nega redefinição confiável ${body.split('\n')[0]}`, async t => {
    const f = fixture(t);
    f.write('ClientProof.bend', f.read('ClientProof.bend') + '\n' + body);
    await rejection(f.manifest(), ['PARSE', 'REDEFINITION']);
  });
}

test('nega alvo enfraquecido pelo gerador do host', async t => {
  const f = fixture(t);
  f.write('Bindings.bend', f.read('Bindings.bend').replace('R.Certifica(I.config(), codigo(), Client.programa(), I.contexto(), I.argumentos())', 'Unit'));
  await rejection(f.manifest(), ['TARGET']);
});

test('nega alvo para outro contexto, argumentos ou programa', async t => {
  for (const [from, to] of [['I.contexto()', 'D.Contexto{"outra", "usuario"}'], ['I.argumentos()', 'D.VAusente{}'], ['Client.programa()', 'S.Programa{c => a => S.Recusar{D.VAusente{}}}']]) {
    const f = fixture(t);
    f.write('Bindings.bend', f.read('Bindings.bend').replace(from, to));
    await rejection(f.manifest(), ['TARGET']);
  }
});

test('nega fonte divergente, mesmo semanticamente equivalente', async t => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend') + '\n# somente comentário\n');
  await rejection(f.manifest(), ['SOURCE_BINDING']);
});

test('nega preenchimento por arquivo não autorizado e alvo ausente', async t => {
  const f = fixture(t);
  const manifest = f.manifest();
  manifest.openTargets['Bindings:certificado'] = 'Client.bend';
  await rejection(manifest, ['REDEFINITION']);
  f.write('ClientProof.bend', f.read('ClientProof.bend').split('\ndef B.termina')[0] + '\n');
  await rejection(f.manifest(), ['OPEN_LAW']);
});

test('nega segunda definição e unsafe no próprio alvo aberto', async t => {
  const duplicated = fixture(t);
  duplicated.write('ClientProof.bend', duplicated.read('ClientProof.bend') + '\ndef B.certificado(s, valido, identidade, n):\n  Unit{}\n');
  await rejection(duplicated.manifest(), ['PARSE', 'REDEFINITION']);
  const unsafe = fixture(t);
  unsafe.write('ClientProof.bend', unsafe.read('ClientProof.bend').replace('def B.certificado(', 'def B.certificado?('));
  await rejection(unsafe.manifest(), ['UNSAFE']);
});

test('captura direta ou indireta de estado privado do host é negada', async t => {
  for (const indirect of [false, true]) {
    const f = fixture(t);
    f.write('Private.bend', 'import Base\nimport ./Dados.bend as D\ndef estado() -> D.Estado:\n  D.Estado{Nil{}, Nil{}}\n', 'host');
    f.write('Instance.bend', 'import ./Private.bend as Secret\n' + f.read('Instance.bend') + '\ndef expor() -> D.Estado:\n  Secret.estado()\n');
    f.write('ClientProof.bend', 'import ./Private.bend as Secret\n' + f.read('ClientProof.bend') + `\ndef capturar() -> D.Estado:\n  ${indirect ? 'I.expor()' : 'Secret.estado()'}\n`);
    const manifest = f.manifest();
    manifest.dependencies.find(d => d.path === 'Instance.bend').exports.push('Instance:expor');
    await rejection(manifest, ['HOST_CAPTURE']);
  }
});

test('captura privada descartada pelo frontend também é negada', async t => {
  const f = fixture(t);
  f.write('Private.bend', 'import Base\ndef segredo() -> String:\n  "estado privado"\n', 'host');
  f.write('ClientProof.bend', 'import ./Private.bend as Secret\n' + f.read('ClientProof.bend') + '\ndef capturar() -> Unit:\n  (x => Unit{})(Secret.segredo())\n');
  await rejection(f.manifest(), ['HOST_CAPTURE']);
});

test('hash do host e contrato permanecem obrigatórios', async t => {
  const f = fixture(t);
  const original = f.manifest();
  f.write('Instance.bend', f.read('Instance.bend') + '\n');
  await rejection(original, ['HASH']);
  f.write('Dados.bend', f.read('Dados.bend') + '\n');
  await rejection(f.manifest(), ['CONTRACT']);
});

test('recusa symlinks, hardlinks e bytes UTF-8 inválidos', async t => {
  for (const kind of ['symbolic', 'hard', 'utf8']) {
    const f = fixture(t);
    const manifest = f.manifest();
    const file = path.join(f.root, 'Client.bend');
    if (kind === 'utf8') {
      fs.writeFileSync(file, Buffer.from([0xff]));
      await rejection(f.manifest(), ['SOURCE_IO']);
    } else {
      fs.renameSync(file, path.join(f.root, 'Original.bend'));
      if (kind === 'hard') fs.linkSync(path.join(f.root, 'Original.bend'), file);
      else fs.symlinkSync('Original.bend', file);
      await rejection(manifest, ['PATH']);
    }
  }
});

test('emissão recusa Book substituído ou modificado após os checkers', async t => {
  const f = fixture(t);
  const a = await admitSubmission(f.manifest());
  assert.throws(() => emitC({ book: a.book }), { code: 'BOOK_CHANGED' });
  a.book.tlds['Client:contar'].u = true;
  assert.throws(() => emitC(a), { code: 'BOOK_CHANGED' });
});

test('bootstrap recusa kernel ausente e ignora BENDTT arbitrário do ambiente', async t => {
  const f = fixture(t);
  await rejection({ ...f.manifest(), toolchain: { kernelPath: path.join(f.root, 'missing') } }, ['TOOLCHAIN']);
  const before = process.env.BENDTT;
  process.env.BENDTT = path.join(f.root, 'arbitrary-not-executed');
  try { assert.equal((await admitSubmission(f.manifest())).report.bendtt, true); }
  finally { if (before === undefined) delete process.env.BENDTT; else process.env.BENDTT = before; }
});

test('falha técnica real de execução do kernel nunca é aceitação', async t => {
  const f = fixture(t);
  const spawn = child.spawnSync;
  child.spawnSync = function (bin, args, options) {
    if (bin === bootstrapInfo().verifier.kernelPath) return { status: null, signal: 'SIGKILL' };
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  try { await rejection(f.manifest(), ['BENDTT_INFRASTRUCTURE']); }
  finally { child.spawnSync = spawn; syncBuiltinESMExports(); }
});

test('CLI produz relatório e C e retorna rejeição em JSON', async t => {
  const f = fixture(t);
  const manifestFile = path.join(f.root, 'host.json');
  fs.writeFileSync(manifestFile, JSON.stringify(f.manifest()));
  const cli = path.join(repo, 'tools/admission/cli.mjs');
  const good = child.spawnSync(process.execPath, [cli, '--manifest', manifestFile, '--emit-c', path.join(f.root, 'out.c')], { encoding: 'utf8', timeout: 30000 });
  assert.equal(good.status, 0, good.stderr);
  assert.equal(JSON.parse(good.stdout).bendtt, true);
  assert.ok(fs.statSync(path.join(f.root, 'out.c')).size > 1000);
  f.write('Client.bend', 'changed source');
  const bad = child.spawnSync(process.execPath, [cli, '--manifest', manifestFile], { encoding: 'utf8', timeout: 30000 });
  assert.equal(bad.status, 2);
  assert.equal(JSON.parse(bad.stderr).code, 'HASH');
});

test('preflight é utilizável separadamente, sem carregar toolchain', t => {
  const f = fixture(t);
  const p = preflight(f.manifest());
  assert.equal(p.records.get('ClientProof.bend').aliases.B, 'Bindings');
  assert.equal(p.records.get('Client.bend').text, f.read('Client.bend'));
});
