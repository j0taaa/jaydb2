// Admit the real recursive fixture with both checkers, then emit that same Book.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { admitSubmission, emitGenericC } from '../../tools/admission/index.mjs';
import { sha256 } from '../../tools/admission/bootstrap.mjs';
import { fixture, repo } from '../admission/helpers.mjs';
const [output] = process.argv.slice(2);
const cleanup = [], f = fixture({ after(fn) { cleanup.push(fn); } });
try {
  const source = fs.readFileSync(path.join(repo, 'tests/native/fixtures/stack_depth.bend'), 'utf8')
    .replace('import Base', 'import Base\nimport ./ClientProof.bend as Proof')
    .replace('../../../native/effects.bend', './Native.bend');
  f.write('Main.bend', source);
  f.write('Native.bend', `import Base
def read() -> IO(List<&2, U32>):
  import "./effects.c"
def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"
`, 'kernel');
  f.write('effects.c', fs.readFileSync(path.join(repo, 'native/effects.c'), 'utf8'));
  const manifest = f.manifest();
  manifest.kernel = { module: 'Native.bend', primitives: ['read', 'write'],
    foreign: { path: 'effects.c', sha256: sha256(f.read('effects.c')) } };
  const admitted = await admitSubmission(manifest), book = admitted.book;
  const backendSha256 = sha256(fs.readFileSync(path.join(repo, 'tools/native/generic.mjs')));
  const emission = await emitGenericC(admitted, { backendSha256 });
  assert.strictEqual(admitted.book, book);
  const report = { primary: admitted.report.primary, bendtt: admitted.report.bendtt,
    targets: admitted.report.targets, sameCheckedBook: emission.sameCheckedBook,
    sourceSetSha256: admitted.report.sourceSetSha256, sourceSha256: sha256(source),
    cSha256: sha256(emission.c) };
  fs.writeFileSync(output, emission.c);
  fs.writeFileSync(output + '.gate.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
} catch (error) {
  console.error(error.stack ?? String(error)); process.exitCode = 1;
} finally { cleanup.reverse().forEach(fn => fn()); }
