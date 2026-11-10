# Application policy: each user operates on their own task table.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S

type Both<-P: Data, -Q: Data> is Data:
  Both{left: P, right: Q}

def fields(l: D.Row) -> List<&2, D.Field>:
  D.Row{k, fs} = l
  fs

def Owner(+us: List<&2, D.Row>, +name: String, l: D.Row) -> Data:
  Both<{D.find_field(fields(l), "owner") == Some{D.VText{name}} : Maybe<&2, D.Value>},
    {D.exists_row(D.find_row(us, name)) == True{} : Bool}>

def Rows(+us: List<&2, D.Row>, +name: String, ls: List<&2, D.Row>) -> Data:
  match ls:
    case Nil{}: Unit
    case Con{l, rest}: Both<Owner(us, name, l), Rows(us, name, rest)>

def Tables(+us: List<&2, D.Row>, ts: List<&2, D.Table>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{D.Table{name, ls}, rest}: Both<Rows(us, name, ls), Tables(us, rest)>

def Owners(s: D.State) -> Data:
  D.State{ts, us} = s
  Tables(us, ts)

def Allowed(ctx: D.Context, op: D.Operation) -> Data:
  D.Context{+id, kind} = ctx
  match op:
    case D.ReadCell{D.Application{name}, k, c}: {name == id : String}
    case D.ViewExistence{D.Application{name}, k}: {name == id : String}
    case D.CountRows{D.Application{name}}: {name == id : String}
    case D.EnumerateKeys{D.Application{name}}: {name == id : String}
    case D.DefineRow{D.Application{name}, k, fs}:
      Both<{name == id : String}, {D.find_field(fs, "owner") == Some{D.VText{id}} : Maybe<&2, D.Value>}>
    case D.RemoveRow{D.Application{name}, k}: {name == id : String}
    case _: {False{} == True{} : Bool}

def AllAllowed(+ctx: D.Context, ts: List<&2, S.OperationEvent>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{S.OperationEvent{op, ef}, rest}: Both<Allowed(ctx, op), AllAllowed(ctx, rest)>

def Rule(h: S.Situation) -> Data:
  match h:
    case S.Stable{s}: Owners(s)
    case S.Executing{s, ctx, code, args, w, ts}: Both<Owners(w), AllAllowed(ctx, ts)>
    case S.Closed{s, ctx, code, args, w, ts, r}: Both<Owners(w), AllAllowed(ctx, ts)>

def config(e: D.Schema, lim: S.Limits, environment: String) -> S.Configuration:
  S.Configuration{e, S.MoreOneLaw{Rule, S.NoneLaw{}}, lim, environment}
