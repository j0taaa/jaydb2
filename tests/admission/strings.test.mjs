import assert from 'node:assert/strict';
import test from 'node:test';
import { fixture } from './helpers.mjs';
import { admitSubmission } from '../../tools/admission/index.mjs';
import { bootstrapInfo, sha256 } from '../../tools/admission/bootstrap.mjs';
import fs from 'node:fs';

function withArgument(t, text) {
  const f = fixture(t);
  const literal = '"' + Array.from(text, c => c === '"' ? '\\"' : c === '\\' ? '\\\\' :
    c.codePointAt(0) < 32 ? `\\u{${c.codePointAt(0).toString(16)}}` : c).join('') + '"';
  f.write('Instance.bend', f.read('Instance.bend').replace('D.VInt{0, 42}', `D.VTexto{${literal}}`));
  f.bindCode();
  return f;
}

for (const [name, text] of [
  ['dez mil caracteres', 'a'.repeat(10000)],
  ['escalares suplementares na fronteira da divisão', 'a'.repeat(4999) + '\u{1f600}' + 'b'.repeat(4999)],
  ['octetos públicos reificados como escalares', String.fromCharCode(...Array.from({length: 256}, (_, i) => i)).repeat(40)],
]) {
  test(`literal grande: ${name}; ambos os verificadores`, async t => {
    const admitted = await admitSubmission(withArgument(t, text).manifest());
    assert.equal(admitted.report.primary, true);
    assert.equal(admitted.report.bendtt, true);
    assert.equal(admitted.report.safeStringsSha256,
      sha256(fs.readFileSync(new URL('../../tools/admission/safe-strings.mjs', import.meta.url))));
  });
}

test('a decomposição não valida igualdade falsa no último escalar', async t => {
  const text = 'a'.repeat(10000);
  const f = withArgument(t, text);
  f.write('Client.bend', f.read('Client.bend') + `
law falsa:
  {${JSON.stringify(text)} == ${JSON.stringify(text.slice(0, -1) + 'b')} : String}
def falsa():
  {==}
`);
  f.bindCode();
  await assert.rejects(admitSubmission(f.manifest()), e => ['PRIMARY_CHECK', 'BENDTT_CHECK'].includes(e.code));
});

test('literal grande não oculta capacidade IO em definição não utilizada', async t => {
  const f = withArgument(t, 'a'.repeat(10000));
  f.write('Client.bend', f.read('Client.bend') + '\ndef hidden() -> IO(Unit):\n  IO.exit(91)\n');
  f.bindCode();
  await assert.rejects(admitSubmission(f.manifest()), e => e.code === 'IO');
});

test('bootstrap usa instalações locais fixadas', () => {
  const info = bootstrapInfo();
  if (!process.env.JAYDB_BEND_SOURCE) assert.match(info.sourceDir, /\/\.tools\/bend-source-2\.0\.39$/);
  if (!process.env.JAYDB_BENDTT) assert.match(info.kernelPath, /\/\.tools\/bendtt-[a-f0-9]{64}$/);
});

test('exaustão da pilha do parser é infraestrutura, sem alegar certificado incorreto', async t => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend') + '\ndef deep() -> Nat:\n  ' + '('.repeat(10000) + '0n' + ')'.repeat(10000) + '\n');
  f.bindCode();
  await assert.rejects(admitSubmission(f.manifest()), e => e.code === 'FRONTEND_INFRASTRUCTURE' && e.phase === 'parse');
});
