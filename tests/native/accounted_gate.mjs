// Both real checkers and the real admission emission boundary, in an isolated
// gate/cache copy. No modification to the shared admission or installed cache.
import fs from 'node:fs';
import path from 'node:path';
import {pathToFileURL} from 'node:url';
import {fixture,repo} from '../admission/helpers.mjs';
const [gateRoot,output,variant]=process.argv.slice(2);
const {admitSubmission,emitGenericC}=await import(pathToFileURL(path.join(gateRoot,'tools/admission/index.mjs')));
const {sha256}=await import(pathToFileURL(path.join(gateRoot,'tools/admission/bootstrap.mjs')));
const cleanup=[],f=fixture({after(fn){cleanup.push(fn);}});
try {
 f.write('Codec.bend',fs.readFileSync(path.join(repo,'src/Codec.bend'),'utf8')
  .replace('../contrato/Bytes.bend','./Bytes.bend').replace('../contrato/Dados.bend','./Dados.bend'),'library');
 f.write('Native.bend',`import Base
 def read() -> IO(List<&2,U32>):
   import "./effects.c"
 def write(bytes: List<&2,U32>) -> IO(Unit):
   import "./effects.c"
 def enter(stage: U32) -> IO(Unit):
   import "./effects.c"
`.replace(/^ /gm,''),'kernel');
 f.write('effects.c',fs.readFileSync(path.join(repo,'native/effects.c'),'utf8'));
 f.write('Main.bend',`import Base
import ./ClientProof.bend as Proof
import ./Native.bend as Native
import ./Codec.bend as C
import ./Bytes.bend as B
import ./Protocolo.bend as P
import ./Dados.bend as D

def optional(r: Maybe<&2, List<&2,U32>>) -> List<&2,U32>:
  match r:
    case None{}:
      [252]
    case Some{bs}:
      bs
def result(r: C.Resultado) -> List<&2,U32>:
  match r:
    case C.Decodificado{v}:
      optional(P.codificar(v))
    case C.Entrada{}:
      [254]
    case C.Limite{}:
      [253]
def decode(bs: List<&2,U32>) -> List<&2,U32>:
  result(C.decodificar(bs,B.Numero64{4294967295,4294967295}))
def append(xs: List<&2,U32>,ys: List<&2,U32>) -> List<&2,U32>:
  match xs:
    case Nil{}:
      ys
    case Con{h,t}:
      Con{h,append(t,ys)}
def local(v: D.Valor) -> List<&2,U32>:
  match v:
    case D.VLista{h,r}:
      [88]
    case _:
      [99]
def dispatch(bs: List<&2,U32>) -> List<&2,U32>:
  match bs:
    case Nil{}:
      decode(Nil{})
    case Con{250,t}:
      # The actual Codec argument excludes this private test prefix.
      decode(t)
    case Con{249,+t}:
      # Two distinct decoder contexts in the same native invocation.
      append(decode(t),decode(t))
    case Con{248,t}:
      # Invalid intermediate client values are permitted by the language.
      # This local constructor is not a decoded wire Campo.
      local(D.VLista{D.VAusente{},D.VInt{0,1}})
    case Con{245,t}:
      result(C.decodificar(t,B.Numero64{0,32}))
    case Con{243,t}:
      result(C.decodificar([0],B.Numero64{0,1}))
    case Con{h,t}:
      decode(Con{h,t})
def run(bytes: List<&2,U32>) -> IO(Unit):
  match bytes:
    case Con{247,t}:
      do IO<Unit>:
        Unit <- Native.enter(1)
        Native.write(dispatch(t))
    case Con{246,t}:
      do IO<Unit>:
        Unit <- Native.enter(1)
        Unit <- Native.enter(2)
        Native.write(dispatch(t))
    case _:
      Native.write(dispatch(bytes))
def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2,U32> <- Native.read()
    run(bytes)
`);
 if(variant==='external-helper')f.write('Main.bend',f.read('Main.bend').replace(
   'local(D.VLista{D.VAusente{},D.VInt{0,1}})',
   'local(C.montar_lista(Con{D.VAusente{},Nil{}},D.VInt{0,1}))'));
 if(variant==='no-codec')f.write('Main.bend',[
  'import Base','import ./ClientProof.bend as Proof','import ./Native.bend as Native',
  'import ./Dados.bend as D','import ./Protocolo.bend as P',
  'def optional(r: Maybe<&2,List<&2,U32>>) -> List<&2,U32>:',
  '  match r:','    case None{}:','      [252]','    case Some{bs}:','      bs',
  'def main() -> IO(Unit):',
  '  Native.write(optional(P.codificar(D.VLista{D.VInt{0,1},D.VListaVazia{}})))',
 ].join('\n')+'\n');
 const manifest=f.manifest();
 manifest.kernel={module:'Native.bend',primitives:['read','write','enter'],foreign:{path:'effects.c',sha256:sha256(f.read('effects.c'))}};
 const admitted=await admitSubmission(manifest),book=admitted.book;
 const backendSha256=sha256(fs.readFileSync(path.join(gateRoot,'tools/native/generic.mjs')));
 const emission=await emitGenericC(admitted,{backendSha256});
 fs.writeFileSync(output,emission.c);

 if(admitted.book!==book || !Object.isFrozen(book) || !emission.sameCheckedBook)throw new Error('Book identity guard');
 if(variant!=='no-codec' && !emission.c.includes('jaydb_codec_accounted(e,'))throw new Error('No actual trusted decoder lowering emitted');
 if(variant==='no-codec' && (!emission.c.includes('JAYDB_NATIVE_ACCOUNTED_EMPTY_V1')
     || emission.c.includes('jaydb_codec_accounted(e,')))throw new Error('Decoder absence was not established');
 if(variant==='external-helper' && !emission.c.includes('JAYDB_NATIVE_ACCOUNTED_UNCOVERED_V1'))
   throw new Error('External helper coverage was silently accepted');
 fs.writeFileSync(output,emission.c);
 const report={primary:admitted.report.primary,bendtt:admitted.report.bendtt,sameCheckedBook:emission.sameCheckedBook,
  checkedBookFrozen:true,backendSha256,cSha256:emission.cSha256,sourceSetSha256:emission.sourceSetSha256,
  trustedCodecEntryUsesRecipe:emission.c.includes('jaydb_codec_accounted(e,'),
  absenceDecodeEstablished:emission.c.includes('JAYDB_NATIVE_ACCOUNTED_EMPTY_V1'),
  uncoveredExternalEntries:emission.c.includes('JAYDB_NATIVE_ACCOUNTED_UNCOVERED_V1'),
  fullExecutableContractProved:false};
 fs.writeFileSync(output+'.checked.json',JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report));
} finally {cleanup.reverse().forEach(f=>f());}
