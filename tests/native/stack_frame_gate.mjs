// Real admission: a wide closure reconstructs its product, retaining whole Terms.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { admitSubmission, emitGenericC } from '../../tools/admission/index.mjs';
import { sha256 } from '../../tools/admission/bootstrap.mjs';
import { fixture, repo } from '../admission/helpers.mjs';
const [output, size = '2800', mode = 'U32'] = process.argv.slice(2);
const count = Number(size);
assert.ok(Number.isSafeInteger(count) && count > 1);
assert.ok(['U32', 'polymorphic'].includes(mode));
const cleanup = [], f = fixture({ after(fn) { cleanup.push(fn); } });
function sum(xs) {
  if (xs.length === 1) return xs[0];
  const middle = Math.floor(xs.length / 2);
  return `U32.add(${sum(xs.slice(0, middle))}, ${sum(xs.slice(middle))})`;
}
try {
  const names = Array.from({ length: count }, (_, i) => 'a' + i);
  const source = mode === 'polymorphic' ? `import Base
import ./ClientProof.bend as Proof
import ./Native.bend as Native

type Payload<-A: Type> is Type:
  Payload{${names.map(n => n + ': A').join(', ')}}

type Holder<-A: Type> is Type:
  Holder{function: Unit -> Payload<A>}

def make(-A: Type, payload: Payload<A>) -> Holder<A>:
  match payload:
    case Payload{${names.join(', ')}}:
      Holder{z => Payload{${names.join(', ')}}}

def invoke(-A: Type, holder: Holder<A>) -> Payload<A>:
  match holder:
    case Holder{function}:
      function(Unit{})

def checksum(payload: Payload<U32>) -> U32:
  match payload:
    case Payload{${names.join(', ')}}:
      ${sum(names)}

def evaluate(+x: U32) -> U32:
  U32.mod(checksum(invoke(U32, make(U32, Payload{${names.map((_, i) => `U32.add(x, ${i})`).join(', ')}}))), 256)

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
` : `import Base
import ./ClientProof.bend as Proof
import ./Native.bend as Native

type Payload is Type:
  Payload{${names.map(n => n + ': U32').join(', ')}}

type Holder is Type:
  Holder{function: U32 -> Payload}

def make(payload: Payload) -> Holder:
  match payload:
    case Payload{${names.join(', ')}}:
      Holder{z => Payload{U32.add(z, a0), ${names.slice(1).join(', ')}}}

def invoke(holder: Holder, z: U32) -> Payload:
  match holder:
    case Holder{function}:
      function(z)

def checksum(payload: Payload) -> U32:
  match payload:
    case Payload{${names.join(', ')}}:
      ${sum(names)}

def evaluate(+x: U32) -> U32:
  U32.mod(checksum(invoke(make(Payload{${names.map((_, i) => `U32.add(x, ${i})`).join(', ')}}), 3)), 256)

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
  const report = { fields: count, mode, primary: admitted.report.primary, bendtt: admitted.report.bendtt,
    targets: admitted.report.targets, sameCheckedBook: emission.sameCheckedBook,
    sourceSetSha256: admitted.report.sourceSetSha256, sourceSha256: sha256(source),
    cSha256: sha256(emission.c) };
  fs.writeFileSync(output, emission.c);
  fs.writeFileSync(output + '.gate.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
} catch (error) {
  console.error(error.stack ?? String(error)); process.exitCode = 1;
} finally { cleanup.reverse().forEach(fn => fn()); }
