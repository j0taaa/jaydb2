from pathlib import Path
import json,os,sys
ROOT=Path(__file__).resolve().parents[3]
SUITE=Path(__file__).resolve().parent
OUT=Path(os.environ.get("JAYDB_INDEX_BENCH_OUTPUT",str(ROOT/"build/library/index-benchmark-run"))).resolve()
STAGE=OUT/'stage'
STAGE.mkdir(parents=True,exist_ok=True)
(OUT/"tmp").mkdir(exist_ok=True)
if (OUT/"results.json").exists():
 raise RuntimeError("Choose a fresh JAYDB_INDEX_BENCH_OUTPUT; existing evidence is not overwritten")
for folder in ['contract','library']:
 for p in (ROOT/folder).glob('*.bend'):
  if p.name=='VERIFY.bend':continue
  (STAGE/p.name).write_text(p.read_text().replace('../contract/','./').replace('../src/','./').replace('../proof/','./'))
for name in ['Termination','ValidationFinal','Free']:
 p=ROOT/'src'/f'{name}.bend';(STAGE/p.name).write_text(p.read_text().replace('../contract/','./'))
for name in ['Orders','Foundations']:
 p=ROOT/'proof'/f'{name}.bend';(STAGE/p.name).write_text(p.read_text().replace('../contract/','./'))
(STAGE/'Completion.bend').write_text((ROOT/'applications/indexed/Completion.bend').read_text())
for name in ['Bench','BenchProof']:(STAGE/(name+'.bend')).write_text((SUITE/(name+'.bend')).read_text())
(STAGE/'Environment.bend').write_text('import Base\ndef identity() -> String: "index-benchmark-proof-only"\n')
(STAGE/'Client.bend').write_text('import Base\nimport ./Semantics.bend as S\nimport ./Bench.bend as Bench\ndef program() -> S.Program: Bench.program()\n')
(STAGE/'Configuration.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
import ./BenchProof.bend as BenchProof

def schema() -> D.Schema:
  D.Schema{[
    D.SchemaTable{"base","id",[D.Column{"email",D.TextValue{},False{}},D.Column{"group",D.TextValue{},False{}},D.Column{"id",D.TextValue{},False{}},D.Column{"pad",D.TextValue{},False{}}]},
    D.SchemaTable{"many_index","id",[D.Column{"id",D.TextValue{},False{}},D.Column{"target",D.TextValue{},False{}},D.Column{"value",D.TextValue{},False{}}]},
    D.SchemaTable{"unique_index","id",[D.Column{"id",D.TextValue{},False{}},D.Column{"target",D.TextValue{},False{}},D.Column{"value",D.TextValue{},False{}}]}]}
def limits() -> S.Limits: S.Limits{65536n,2097152n,65536n}
def config() -> S.Configuration: L.configuration(schema(),limits(),E.identity())
''')
(STAGE/'Seed.bend').write_text('''import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C

def state() -> D.State:
  D.State{[D.Table{"base",[]},D.Table{"many_index",[]},D.Table{"unique_index",[]}],[D.Row{"bench",[D.Field{"credential",D.VText{"benchmark-token"}},D.Field{"id",D.VText{"bench"}},D.Field{"kind",D.VText{"user"}}]}]}
law initial_valid: R.Valid(C.config(),state())
def initial_valid(): L.Both{{==},Unit{}}
''')
(STAGE/'Instance.bend').write_text('import Base\nimport ./Data.bend as D\nimport ./Semantics.bend as S\nimport ./Configuration.bend as C\ndef config() -> S.Configuration: C.config()\ndef context() -> D.Context: D.Context{"bench","user"}\ndef arguments() -> D.Value: D.VAbsent{}\n')
code=(STAGE/'Client.bend').read_text()
literal='"'+''.join('\\"' if c=='"' else '\\\\' if c=='\\' else f'\\u{{{ord(c):02x}}}' if ord(c)<32 else c for c in code)+'"'
(STAGE/'Bindings.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Interface.bend as F
import ./Instance.bend as I
import ./Client.bend as Client

def code() -> String: '''+literal+'''
law certificate:
  for ctx:D.Context
  for args:D.Value
  R.Certifies(I.config(),code(),Client.program(),ctx,args)
law terminates: F.ProgramTerminates(I.config(),Client.program())
''')
(STAGE/'ClientProof.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Termination.bend as T
import ./Interface.bend as F
import ./Completion.bend as E
import ./Bench.bend as Bench
import ./BenchProof.bend as Proof
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B
import ./Client.bend as Client

def B.certificate(ctx,args,s,valid,identity,n):
  L.execution_trace_free_covers_prefixes_and_final(S.execute(n,Client.program(),C.schema(),s,ctx,args),C.schema(),C.limits(),S.environment(I.config()),s,ctx,B.code(),args)
def terminate(+s:D.State,+ctx:D.Context,+args:D.Value,h:E.Complete(S.start(Client.program(),ctx,args),C.schema(),s,Nil{})) -> F.Terminates(Client.program(),C.schema(),s,ctx,args):
  match h:
    case (n,w,events,r,eq): T.witness_program(n,Client.program(),C.schema(),s,ctx,args,(w,events,r,eq))
def B.terminates(s,ctx,args):
  +state=s
  +context=ctx
  +arguments=args
  terminate(state,context,arguments,Proof.complete(Bench.command(arguments),C.schema(),state,Nil{}))
''')
(STAGE/'Check.bend').write_text('import ./ClientProof.bend as Proof\nimport ./Seed.bend as Seed\n')
print(STAGE/'Check.bend')

# A separate proof root for the submitted batch program; public configuration
# stays identical to the single-query sessions.
import shutil
batch=OUT/'batch-proof'
shutil.copytree(STAGE,batch,dirs_exist_ok=True)
(batch/'Client.bend').write_text((SUITE/'BatchClient.bend').read_text())
(batch/'ClientProof.bend').write_text((SUITE/'BatchProof.bend').read_text())
code=(batch/'Client.bend').read_text()
literal='"'+''.join('\\"' if c=='"' else '\\\\' if c=='\\' else f'\\u{{{ord(c):02x}}}' if ord(c)<32 else c for c in code)+'"'
bindings=(batch/'Bindings.bend').read_text()
a=bindings.index('def code() -> String:');b=bindings.index('\nlaw certificate:',a)
(batch/'Bindings.bend').write_text(bindings[:a]+'def code() -> String: '+literal+bindings[b:])
print(batch/'Check.bend')
