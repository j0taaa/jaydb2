import fs from 'node:fs';
import assert from 'node:assert/strict';
import test from 'node:test';
import { fixture, repo } from './helpers.mjs';
import { admitSubmission } from '../../tools/admission/index.mjs';

function setup(t) {
  const f = fixture(t);
  f.write('Instance.bend', f.read('Instance.bend').replace(
    'S.Limites{256n, 256n, 256n}',
    'S.Limites{32768n, 65536n, 32768n}'));
  f.write('Client.bend', fs.readFileSync(repo + 'examples/sem-observacoes/Sucesso.bend', 'utf8'));
  f.write('ClientProof.bend', fs.readFileSync(repo + 'examples/sem-observacoes/SucessoProof.bend', 'utf8').replace('import ./Configuration.bend as C\n', ''));
  f.bindCode();
  return f;
}

test('certificado de sucesso com limites reais preserva subtermos rígidos; BendTT aceita', async t => {
  const admitted = await admitSubmission(setup(t).manifest());
  assert.equal(admitted.report.primary, true);
  assert.equal(admitted.report.bendtt, true);
  assert.match(admitted.report.toolchainSha256, /^[a-f0-9]{64}$/);
});

test('otimização da conversão não torna uma prova incorreta válida', async t => {
  const f = setup(t);
  f.write('ClientProof.bend', f.read('ClientProof.bend').replace('S.Resposta{S.Sucesso{}, D.VInt{0, 6}}, {==}', 'S.Resposta{S.Sucesso{}, D.VInt{0, 7}}, {==}'));
  await assert.rejects(admitSubmission(f.manifest()), e => ['PRIMARY_CHECK', 'BENDTT_CHECK'].includes(e.code));
});

test('subtermos distintos continuam distintos na presença dos numerais grandes', async t => {
  const f = setup(t);
  f.write('Client.bend', f.read('Client.bend').replace('somar([1, 2, 3], 0)', 'somar([1, 2, 4], 0)'));
  f.bindCode();
  await assert.rejects(admitSubmission(f.manifest()), e => ['PRIMARY_CHECK', 'BENDTT_CHECK'].includes(e.code));
});
