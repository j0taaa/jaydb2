// Real Codec, both checkers, same admitted Book. Inspection emits identical C.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { admitSubmission, emitGenericC } from '../../tools/admission/index.mjs';
import { sha256 } from '../../tools/admission/bootstrap.mjs';
import { loadConstructionMetadataCompiler } from '../../tools/native/construction_metadata.mjs';
import { fixture, repo } from '../admission/helpers.mjs';
const [output] = process.argv.slice(2);
const cleanup = [], f = fixture({ after(fn) { cleanup.push(fn); } });
try {
  f.write('Codec.bend', fs.readFileSync(path.join(repo, 'src/Codec.bend'), 'utf8')
    .replace('../contrato/Bytes.bend', './Bytes.bend')
    .replace('../contrato/Dados.bend', './Dados.bend'), 'library');
  f.write('Main.bend', `import Base
import ./ClientProof.bend as Proof
import ./Native.bend as Native
import ./Codec.bend as C
import ./Bytes.bend as B
import ./Protocolo.bend as P

def optional(r: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case None{}:
      [252]
    case Some{bs}:
      bs
def result(r: C.Resultado) -> List<&2, U32>:
  match r:
    case C.Decodificado{v}:
      optional(P.codificar(v))
    case C.Entrada{}:
      [254]
    case C.Limite{}:
      [253]
def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(result(C.decodificar(bytes, B.Numero64{4294967295, 4294967295})))
`);
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
  const foreign = new Map();
  for (const t of Object.values(book.tlds)) for (const file of t.i ?? []) {
    if (file.endsWith('.c') && fs.existsSync(file) && fs.statSync(file).isFile()) foreign.set(file, {
      path: fs.realpathSync(file), source: fs.readFileSync(file, 'utf8') });
  }
  const backendSha256 = sha256(fs.readFileSync(path.join(repo, 'tools/native/generic.mjs')));
  const directory = path.join(process.env.JAYDB_BEND_SOURCE ?? path.join(repo, '.tools/bend-source-2.0.39'), 'bend2');
  // Production emission first checks its own seal/hashes, closes the Book and
  // emits it. Inspection cannot precede that boundary or update its seal.
  const normal = await emitGenericC(admitted, { backendSha256 });
  assert(Object.isFrozen(book));
  const inspection = await loadConstructionMetadataCompiler(directory);
  const metadata = inspection.compile_book(book, [...foreign]);
  assert.strictEqual(admitted.book, book);
  const body = normal.c.replace(/^(?:\/\/ JAYDB_NATIVE_[^\n]*\n)+/, '');
  assert.equal(metadata.c, body, 'Inspection must preserve exact emitted C body');
  const report = { primary: admitted.report.primary, bendtt: admitted.report.bendtt,
    sameCheckedBook: normal.sameCheckedBook, inspectionUsedSameBookObject: true,
    checkedBookFrozenBeforeInspection: true,
    emittedCUnchanged: true, sourceSetSha256: admitted.report.sourceSetSha256,
    cSha256: sha256(normal.c), coreCompilerSha256: metadata.coreSourceSha256,
    inspectionCompilerSha256: metadata.inspectionSourceSha256,
    noRuntimeEventsClaimed: true, sites: metadata.sites };
  fs.writeFileSync(output, normal.c);
  fs.writeFileSync(output + '.constructors.json', JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ ...report, sites: report.sites.length }));
} catch (error) {
  console.error(error.stack ?? String(error)); process.exitCode = 1;
} finally { cleanup.reverse().forEach(fn => fn()); }
