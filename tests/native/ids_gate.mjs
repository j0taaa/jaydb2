// Test only: actual admission through both checkers, then emission of that Book.
// Generates large source fixtures rather than committing 65,537 boilerplate rows.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { admitSubmission, emitGenericC, emitC } from '../../tools/admission/index.mjs';
import { sha256 } from '../../tools/admission/bootstrap.mjs';
import { fixture, repo } from '../admission/helpers.mjs';

const [output, size = '65537', mode = 'generic'] = process.argv.slice(2);
const count = Number(size);
assert.ok(Number.isSafeInteger(count) && count >= 4);
const cleanup = [];
const f = fixture({ after(fn) { cleanup.push(fn); } });
const last = count - 1, previous = count - 2;
try {
  // Each ADT stays shallow enough for the real Safe serializer. A single ADT
  // with 65k arms hits a separate frontend stack limit before BendTT runs.
  const groups = Math.ceil(count / 512), types = [], leaves = [], fields = [], names = [];
  let start = 0;
  for (let g = 0; g < groups; ++g) {
    const width = Math.floor(count / groups) + Number(g < count % groups);
    const constructors = [`  C${start}{tail: Many${g}}`];
    for (let i = start + 1; i < start + width; ++i) constructors.push(
      `  C${i}` + (i >= previous ? `{value: U32, tail: Many${g}}` : '{}'));
    types.push(`type Many${g} is Type:\n` + constructors.join('\n'));
    fields.push(`f${g}: Many${g}`);
    names.push(`f${g}`);
    leaves.push(`C${start + 1}{}`);
    start += width;
  }
  // A recursive root forces BOX, so this test does not depend on a wide
  // function/return layout and can isolate the ID representation.
  types.push('type Root is Type:\n  Root{' + [...fields, 'tail: List<Root>'].join(', ') + '}');
  const lastLeaf = leaves.pop();
  const many = 'import Base\n\n' + types.join('\n\n') + `

def root(x: Many${groups - 1}) -> Root:
  Root{${[...leaves, 'x', 'Nil{}'].join(', ')}}

def unroot(value: Root) -> Many${groups - 1}:
  match value:
    case Root{${[...names, 'tail'].join(', ')}}:
      f${groups - 1}

def make(bytes: List<&2, U32>) -> Root:
  match bytes:
    case Nil{}:
      root(C${last}{241, ${lastLeaf}})
    case Con{h, t}:
      root(C${previous}{h, ${lastLeaf}})

def inspect(value: Many${groups - 1}) -> U32:
  match value:
    case C${last}{x, tail}:
      x
    case C${previous}{x, tail}:
      U32.xor(x, 128)
    case _:
      7
`;
  f.write('Many.bend', many, 'library');
  f.write('Native.bend', `import Base

def read() -> IO(List<&2, U32>):
  import "./effects.c"

def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"
`, 'kernel');
  f.write('effects.c', fs.readFileSync(path.join(repo, 'native/effects.c'), 'utf8'));
  f.write('Main.bend', `import Base
import ./ClientProof.bend as Proof
import ./Native.bend as Native
import ./Many.bend as M

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([M.inspect(M.unroot(M.make(bytes)))])
`);
  const manifest = f.manifest();
  manifest.kernel = { module: 'Native.bend', primitives: ['read', 'write'],
    foreign: { path: 'effects.c', sha256: sha256(f.read('effects.c')) } };
  const started = performance.now();
  const admitted = await admitSubmission(manifest);
  const book = admitted.book;
  const report = { constructors: count, manySourceSha256: sha256(many),
    manySourceBytes: Buffer.byteLength(many), primary: admitted.report.primary,
    bendtt: admitted.report.bendtt, sourceSetSha256: admitted.report.sourceSetSha256,
    toolchainSha256: admitted.report.toolchainSha256,
    targets: admitted.report.targets, admissionMs: performance.now() - started };
  try {
    const backendSha256 = sha256(fs.readFileSync(path.join(repo, 'tools/native/generic.mjs')));
    const emission = mode === 'official' ? { c: emitC(admitted) }
      : await emitGenericC(admitted, { backendSha256 });
    assert.strictEqual(admitted.book, book);
    if (mode !== 'official') {
      assert.equal(emission.sameCheckedBook, true);
      assert.strictEqual(await emitGenericC(admitted, { backendSha256 }), emission);
    }
    fs.writeFileSync(output, emission.c);
    Object.assign(report, { emitted: true, cSha256: sha256(emission.c),
      sameCheckedBook: mode !== 'official' && emission.sameCheckedBook,
      derivedCompilerSha256: emission.compilerSha256 });
  } catch (error) {
    Object.assign(report, { emitted: false, errorCode: error.code, error: error.message });
    if (mode !== 'official') throw error;
    assert.equal(error.code, 'COMPILE');
    assert.match(error.message, /an id over 65535/);
  }
  fs.writeFileSync(output + '.gate.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
} catch (error) {
  console.error(error.stack ?? String(error));
  process.exitCode = 1;
} finally { cleanup.reverse().forEach(fn => fn()); }
