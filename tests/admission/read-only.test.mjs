import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { admitSubmission } from '../../tools/admission/index.mjs';
import { fixture, repo } from './helpers.mjs';

function readFixture(t) {
  const f = fixture(t);
  f.write('ReadOnly.bend', fs.readFileSync(repo + '/src/ReadOnly.bend', 'utf8').replaceAll('../contract/', './'), 'library');
  f.write('ReadOnlyContract.bend', fs.readFileSync(repo + '/contract/ReadOnlyContract.bend', 'utf8'), 'library');
  f.write('Bindings.bend', 'import ./ReadOnly.bend as RO\n' + f.read('Bindings.bend').replace(
    'R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())',
    '@ctx: D.Context -> @args: D.Value -> R.Certifies(I.config(), code(), Client.program(), ctx, args)') +
    '\nlaw read_only:\n  RO.Program(Client.program())\n');
  f.write('ClientProof.bend', f.read('ClientProof.bend').replace(
    'def B.certificate(s, valid, identity, n):', 'def B.certificate(ctx, args, s, valid, identity, n):') +
    '\ndef B.read_only(ctx, args):\n  (1n, Unit{})\n');
  f.write('Bindings.bend', f.read('Bindings.bend') + '\ndef proof_source() -> String:\n  ' + JSON.stringify(f.read('ClientProof.bend')) + '\n');
  const manifest = () => ({ ...f.manifest(), certificateMode: 'universal', readOnly: true,
    openTargets: { ...f.manifest().openTargets, 'Bindings:read_only': 'ClientProof.bend' } });
  return { f, manifest };
}
const rejects = (m, code) => assert.rejects(admitSubmission(m), e => e.code === code);

test('read-only admission checks an additional universal source-bound law', async t => {
  const { manifest } = readFixture(t);
  const result = await admitSubmission(manifest());
  assert.equal(result.report.readOnly, true);
  assert.equal(result.report.certificateMode, 'universal');
  assert.ok(result.report.targets.includes('Bindings:read_only'));
});

test('read flag cannot substitute a predicate, target, proof or administrator certificate', async t => {
  {
    const { f, manifest } = readFixture(t);
    f.write('ReadOnly.bend', f.read('ReadOnly.bend').replace('C.Program(p)', 'Unit'));
    await rejects(manifest(), 'READ_ONLY');
  }
  {
    const { f, manifest } = readFixture(t);
    f.write('ReadOnlyContract.bend', f.read('ReadOnlyContract.bend').replace('case 0n: Empty', 'case 0n: Unit'));
    await rejects(manifest(), 'CONTRACT');
  }
  {
    const { f, manifest } = readFixture(t);
    f.roles.delete('ReadOnlyContract.bend');
    await rejects(manifest(), 'READ_ONLY');
  }
  {
    const { f, manifest } = readFixture(t);
    f.write('Bindings.bend', f.read('Bindings.bend').replace('RO.Program(Client.program())', 'Unit'));
    await rejects(manifest(), 'TARGET');
  }
  {
    const { f, manifest } = readFixture(t);
    f.write('ClientProof.bend', f.read('ClientProof.bend') + '\n# altered proof\n');
    await rejects(manifest(), 'SOURCE_BINDING');
  }
  {
    const { f, manifest } = readFixture(t);
    f.write('Client.bend', f.read('Client.bend') + '\n# altered source\n');
    await rejects(manifest(), 'SOURCE_BINDING');
  }
  {
    const { f, manifest } = readFixture(t);
    f.write('ClientProof.bend', f.read('ClientProof.bend').replace('(1n, Unit{})', '(0n, Unit{})'));
    f.write('Bindings.bend', f.read('Bindings.bend').replace(/def proof_source\(\)[\s\S]*/, 'def proof_source() -> String:\n  ' + JSON.stringify(f.read('ClientProof.bend')) + '\n'));
    await rejects(manifest(), 'PRIMARY_CHECK');
  }
  {
    const { f, manifest } = readFixture(t);
    const proof = f.read('ClientProof.bend');
    f.write('ClientProof.bend', proof.slice(0, proof.indexOf('def B.certificate')) +
      'def B.certificate(ctx, args, s, valid, identity, n):\n  Unit{}\n' +
      proof.slice(proof.indexOf('def B.terminates')));
    const bindings = f.read('Bindings.bend');
    f.write('Bindings.bend', bindings.slice(0, bindings.indexOf('def proof_source')) +
      'def proof_source() -> String:\n  ' + JSON.stringify(f.read('ClientProof.bend')) + '\n');
    await rejects(manifest(), 'PRIMARY_CHECK');
  }
  const { manifest } = readFixture(t);
  await rejects({ ...manifest(), certificateMode: 'concrete' }, 'MANIFEST');
});
