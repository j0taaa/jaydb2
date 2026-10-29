// Real admission of a function closing over independently named payload fields.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { admitSubmission, emitGenericC, emitC } from '../../tools/admission/index.mjs';
import { sha256 } from '../../tools/admission/bootstrap.mjs';
import { fixture, repo } from '../admission/helpers.mjs';

const [output, size = '248', mode = 'generic', fieldType = 'U32'] = process.argv.slice(2);
assert.ok(fieldType === 'U32' || fieldType === 'Nat');
const numeric = fieldType, literal = n => String(n) + (numeric === 'Nat' ? 'n' : '');
const count = Number(size);
assert.ok(Number.isSafeInteger(count) && count > 1);
const cleanup = [], f = fixture({ after(fn) { cleanup.push(fn); } });
function sum(xs) {
  if (xs.length === 1) return xs[0];
  const middle = Math.floor(xs.length / 2);
  return `${numeric}.add(${sum(xs.slice(0, middle))}, ${sum(xs.slice(middle))})`;
}
try {
  const names = Array.from({ length: count }, (_, i) => 'a' + i);
  f.write('Native.bend', `import Base
def read() -> IO(List<&2, U32>):
  import "./effects.c"
def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"
`, 'kernel');
  f.write('effects.c', fs.readFileSync(path.join(repo, 'native/effects.c'), 'utf8'));
  const main = `import Base
import ./ClientProof.bend as Proof
import ./Native.bend as Native

type Payload is Type:
  Payload{${names.map(n => n + ': ' + numeric).join(', ')}}

type Holder is Type:
  Holder{function: ${numeric} -> ${numeric}}

def make(payload: Payload) -> Holder:
  match payload:
    case Payload{${names.join(', ')}}:
      Holder{z => ${numeric}.add(z, ${sum(names)})}

def invoke(holder: Holder, z: ${numeric}) -> ${numeric}:
  match holder:
    case Holder{function}:
      function(z)

def evaluate(+x: U32) -> U32:
  U32.mod(${numeric === 'Nat' ? 'U32.from_nat(' : ''}invoke(make(Payload{${names.map((_, i) => `${numeric}.add(${numeric === 'Nat' ? 'U32.to_nat(x)' : 'x'}, ${literal(i)})`).join(', ')}}), ${literal(3)})${numeric === 'Nat' ? ')' : ''}, 256)

def first(bytes: List<&2, U32>) -> U32:
  match bytes:
    case Nil{}:
      0
    case Con{x, tail}:
      x

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([evaluate(first(bytes))])
`;
  f.write('Main.bend', main);
  const manifest = f.manifest();
  manifest.kernel = { module: 'Native.bend', primitives: ['read', 'write'],
    foreign: { path: 'effects.c', sha256: sha256(f.read('effects.c')) } };
  const admitted = await admitSubmission(manifest), book = admitted.book;
  const report = { payloadFields: count, fieldType, sourceSha256: sha256(main),
    primary: admitted.report.primary, bendtt: admitted.report.bendtt,
    sourceSetSha256: admitted.report.sourceSetSha256, targets: admitted.report.targets };
  try {
    const backendSha256 = sha256(fs.readFileSync(path.join(repo, 'tools/native/generic.mjs')));
    const emission = mode === 'official' ? { c: emitC(admitted) }
      : await emitGenericC(admitted, { backendSha256 });
    assert.strictEqual(admitted.book, book);
    fs.writeFileSync(output, emission.c);
    Object.assign(report, { emitted: true, sameCheckedBook: emission.sameCheckedBook,
      cSha256: sha256(emission.c), derivedCompilerSha256: emission.compilerSha256 });
  } catch (error) {
    Object.assign(report, { emitted: false, errorCode: error.code, error: error.message });
    if (mode === 'generic') throw error;
    assert.equal(error.code, 'COMPILE');
    assert.match(error.message, /an arity over 247/);
  }
  fs.writeFileSync(output + '.gate.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
} catch (error) {
  console.error(error.stack ?? String(error)); process.exitCode = 1;
} finally { cleanup.reverse().forEach(fn => fn()); }
