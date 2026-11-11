"""Small benchmark packages, using the repository's actual proof combinators."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def universal(proof):
    return proof.replace('def B.certificate(s, valid, identity, n):',
        'def B.certificate(ctx, args, s, valid, identity, n):\n  +ctx = ctx\n  +args = args').replace(
        'def B.certificate(s,valid,identity,n):',
        'def B.certificate(ctx,args,s,valid,identity,n):\n  +ctx=ctx\n  +args=args').replace(
        'I.context()', 'ctx').replace('I.arguments()', 'args')


def package(directory, kind, rows=10, state_limit=65536):
    directory.mkdir(parents=True, exist_ok=True)
    if kind in ('indexed', 'voucher'):
        if kind == 'indexed':
            from applications.indexed.check import prepare
        else:
            from applications.vouchers.check import prepare
        prepare(directory)
    else:
        point_package(directory, kind == 'policy', rows, state_limit)
    proof = (directory/'ClientProof.bend').read_text()
    (directory/'PreparedProof.bend').write_text(universal(proof))
    return directory


def point_package(d, policy, rows, state_limit):
    # Own table = own rows, following the existing tasks/access application law.
    # No owner lookup is hidden in the client or performed by the Python harness.
    names = ['alice', 'bob'] if policy else ['cells']
    tables = ','.join('table("'+n+'")' for n in names)
    config = '''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E
'''
    if policy:
        original = (ROOT/'examples/access/Configuration.bend').read_text()
        start, end = original.index('type Both'), original.index('def schema()')
        config += original[start:end].replace('D.Users{}', 'D.Application{owner}').replace(
            '{key == id : String}', '{owner == id : String}').replace('"credential"', '"value"')
    if policy:
        # The same ownership requirement applies to certified setup operations.
        # Timed ReadCell/DefineColumn cases and their column checks are unchanged.
        config=config.replace('    case _:', '''    case D.DefineRow{D.Application{owner}, key, fields}:
      Both<{owner == id : String}, Unit>
    case D.CountRows{D.Application{owner}}:
      Both<{owner == id : String}, Unit>
    case _:''',1)
    config += '''
def table(name:String) -> D.SchemaTable:
  D.SchemaTable{name,"id",[D.Column{"id",D.TextValue{},False{}},D.Column{"value",D.Integer{},False{}}]}
def schema() -> D.Schema:
  D.Schema{['''+tables+''']}
def limits() -> S.Limits:
  S.Limits{65536n,'''+str(state_limit)+'''n,32768n}
def config() -> S.Configuration:
  S.Configuration{schema(),'''+('S.MoreOneLaw{Accesses,S.NoneLaw{}}' if policy else 'S.NoneLaw{}')+''',limits(),E.identity()}
'''
    (d/'Configuration.bend').write_text(config)
    users = '''[
    D.Row{"alice",[D.Field{"credential",D.VText{"alice-token"}},D.Field{"id",D.VText{"alice"}},D.Field{"kind",D.VText{"user"}}]},
    D.Row{"bob",[D.Field{"credential",D.VText{"bob-token"}},D.Field{"id",D.VText{"bob"}},D.Field{"kind",D.VText{"user"}}]}]'''
    # The exact seed literal and its validity witness are checked normally.
    seed = '''import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C

def state() -> D.State:
  D.State{[''' + ','.join('D.Table{"'+name+'",['+','.join(
        'D.Row{"k'+str(i).zfill(6)+'",[D.Field{"id",D.VText{"k'+str(i).zfill(6)+'"}},D.Field{"value",D.VInt{0,0}}]}'
        for i in range(rows))+']}' for name in names)+'''],'''+users+'''}
law initial_valid:
  R.Valid(C.config(),state())
def initial_valid():
  L.Both{{==},'''+('L.Both{Unit{},Unit{}}' if policy else 'Unit{}')+'''}
'''
    (d/'Seed.bend').write_text(seed)
    client = '''import Base
import ./Data.bend as D
import ./Semantics.bend as S

def response(r:S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{v}}: S.Finish{v}
    case S.UnitValue{}: S.Finish{D.VBool{True{}}}
    case _: S.Refuse{D.VAbsent{}}

type Command is Data:
  Read{key:String}
  Update{key:String,hi:U32,lo:U32}
  Invalid{}

def analyze(args:D.Value) -> Command:
  match args:
    case D.VList{D.VText{"read"},D.VList{D.VText{key},D.VListEmpty{}}}: Read{key}
    case D.VList{D.VText{"update"},D.VList{D.VText{key},D.VList{D.VInt{hi,lo},D.VListEmpty{}}}}: Update{key,hi,lo}
    case _: Invalid{}

def command(owner:String,p:Command) -> S.Action:
  match p:
    case Read{key}:
      S.Access{D.ReadCell{D.Application{owner},key,"value"},response}
    case Update{key,hi,lo}:
      S.Access{D.DefineColumn{D.Application{owner},key,"value",D.VInt{hi,lo}},response}
    case Invalid{}: S.Refuse{D.VAbsent{}}

def start(ctx:D.Context,args:D.Value) -> S.Action:
  command('''+('D.context_id(ctx)' if policy else '"cells"')+''',analyze(args))
def program() -> S.Program:
  S.Program{start}
'''
    (d/'Client.bend').write_text(client)
    if not policy:
        proof = '''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as Free
import ./Termination.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificate(s, valid, identity, n):
  Free.execution_trace_free_covers_prefixes_and_final(S.execute(n,Client.program(),C.schema(),s,I.context(),I.arguments()),C.schema(),C.limits(),S.environment(I.config()),s,I.context(),B.code(),I.arguments())

def response_finite(r:S.Return) -> T.Finite(1n,Client.response(r)):
  match r:
    case S.UnitValue{}: Unit{}
    case S.Datum{obs}:
      match obs:
        case D.Cell{v}: Unit{}
        case D.RowAbsent{}: Unit{}
        case D.Existence{b}: Unit{}
        case D.Count{n}: Unit{}
        case D.Keys{xs}: Unit{}

def finite(owner:String,p:Client.Command) -> T.Finite(2n,Client.command(owner,p)):
  match p:
    case Client.Read{key}: response_finite
    case Client.Update{key,hi,lo}: response_finite
    case Client.Invalid{}: Unit{}

def B.terminates(s,ctx,args):
  +ctx=ctx
  +args=args
  T.program_finite(2n,Client.program(),C.schema(),s,ctx,args,finite("cells",Client.analyze(args)))
'''
    else:
        old = (ROOT/'examples/access/ClientProof.bend').read_text()
        # Reuse prefix induction, finalization and finite-action proof unchanged.
        a, b = old.index('def response_safe'), old.index('def prefix(')
        proof = old[:a]+'''def response_safe(r:S.Return,ctx:D.Context) -> Safe(1n,ctx,Client.response(r)):
  match r:
    case S.UnitValue{}: Unit{}
    case S.Datum{obs}:
      match obs:
        case D.Cell{v}: Unit{}
        case D.RowAbsent{}: Unit{}
        case D.Existence{b}: Unit{}
        case D.Count{n}: Unit{}
        case D.Keys{xs}: Unit{}

def command_safe(+id:String,kind:String,p:Client.Command) -> Safe(2n,D.Context{id,kind},Client.command(id,p)):
  match p:
    case Client.Read{key}:
      L.Both{C.Both{{==},{==}}, r => response_safe(r,D.Context{id,kind})}
    case Client.Update{key,hi,lo}:
      L.Both{C.Both{{==},{==}}, r => response_safe(r,D.Context{id,kind})}
    case Client.Invalid{}: Unit{}

def program_safe(+ctx:D.Context,args:D.Value) -> Safe(2n,ctx,S.start(Client.program(),ctx,args)):
  match ctx:
    case D.Context{id,kind}: command_safe(id,kind,Client.analyze(args))

'''+old[b:]
        proof = proof.replace('safe(3n,', 'safe(2n,').replace('finite(3n,', 'finite(2n,').replace('T.program_finite(3n,', 'T.program_finite(2n,')
    (d/'ClientProof.bend').write_text(proof)


def bulk_population(point_proof):
    """Populate a valid empty seed, reusing Free and finite-action induction."""
    code='''import Base
import ./Data.bend as D
import ./Semantics.bend as S

def rows(value:D.Value) -> List<&2,D.Row>:
  match value:
    case D.VList{D.VText{+key},rest}:
      D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"value",D.VInt{0,0}}]} <> rows(rest)
    case _: Nil{}

def response(r:S.Return) -> S.Action:
  match r:
    case S.Datum{D.Count{n}}: S.Finish{D.VInt{0,U32.from_nat(n)}}
    case _: S.Refuse{D.VAbsent{}}

def run(rs:List<&2,D.Row>) -> S.Action:
  match rs:
    case Nil{}: S.Access{D.CountRows{D.Application{"cells"}},response}
    case Con{D.Row{key,fields},rest}:
      S.Access{D.DefineRow{D.Application{"cells"},key,fields},ignored => run(rest)}

def depth(rs:List<&2,D.Row>) -> Nat:
  match rs:
    case Nil{}: 2n
    case Con{row,rest}: Succ{depth(rest)}

def program() -> S.Program:
  S.Program{ctx => args => run(rows(args))}
'''
    # The Free certificate quantifies over every program trace. The existing
    # one-step response proof is reused, then structural list induction proves
    # the exact number of accesses for this particular population program.
    if not point_proof: return code,''
    prefix=point_proof.split('def response_finite')[0]
    response=point_proof.split('def response_finite')[1].split('def finite(')[0]
    proof=prefix+'def response_finite'+response+'''def finite(rs:List<&2,D.Row>) -> T.Finite(Client.depth(rs),Client.run(rs)):
  match rs:
    case Nil{}: response_finite
    case Con{D.Row{key,fields},+rest}: r => finite(rest)

def B.terminates(s,ctx,args):
  +ctx=ctx
  +args=args
  T.program_finite(Client.depth(Client.rows(args)),Client.program(),C.schema(),s,ctx,args,finite(Client.rows(args)))
'''
    return code,universal(proof)


def owner_population(policy_proof):
    """The access example's induction, specialized to certified own-row inserts."""
    code,_=bulk_population('')
    code=code.replace('def run(rs:', 'def run(+owner:String,rs:')
    code=code.replace('D.Application{"cells"}', 'D.Application{owner}')
    code=code.replace('ignored => run(rest)', 'ignored => run(owner,rest)')
    code=code.replace('S.Program{ctx => args => run(rows(args))}', 'S.Program{ctx => args => run(D.context_id(ctx),rows(args))}')
    a=policy_proof.index('def response_safe');b=policy_proof.index('def prefix(')
    proof=policy_proof[:a]+'''def response_safe(r:S.Return,ctx:D.Context) -> Safe(1n,ctx,Client.response(r)):
  match r:
    case S.UnitValue{}: Unit{}
    case S.Datum{obs}:
      match obs:
        case D.Cell{v}: Unit{}
        case D.RowAbsent{}: Unit{}
        case D.Existence{b}: Unit{}
        case D.Count{n}: Unit{}
        case D.Keys{xs}: Unit{}

def run_safe(+id:String,+kind:String,rs:List<&2,D.Row>) -> Safe(Client.depth(rs),D.Context{id,kind},Client.run(id,rs)):
  match rs:
    case Nil{}: L.Both{C.Both{{==},Unit{}},r => response_safe(r,D.Context{id,kind})}
    case Con{D.Row{key,fields},+rest}:
      L.Both{C.Both{{==},Unit{}},r => run_safe(id,kind,rest)}

def program_safe(ctx:D.Context,args:D.Value) -> Safe(Client.depth(Client.rows(args)),ctx,S.start(Client.program(),ctx,args)):
  match ctx:
    case D.Context{id,kind}: run_safe(id,kind,Client.rows(args))

'''+policy_proof[b:]
    proof=proof.replace('safe(2n, n,', 'safe(Client.depth(Client.rows(I.arguments())), n,')
    proof=proof.replace('T.program_finite(2n,', 'T.program_finite(Client.depth(Client.rows(arguments)),')
    proof=proof.replace('finite(2n, S.start', 'finite(Client.depth(Client.rows(arguments)), S.start')
    return code,universal(proof)
