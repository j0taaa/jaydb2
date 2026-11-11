# Row security on ONE shared table; no implicit administrator exception.
import Base
import ./Data.bend as D
import ./Semantics.bend as S

type Both<-P: Data, -Q: Data> is Data:
  Both{left: P, right: Q}

# Two addressable slots per owner make private listing exhaustive without a scan.
def key_owner(k: String) -> String:
  match k:
    case "alice/1": "alice"
    case "alice/2": "alice"
    case "bob/1": "bob"
    case "bob/2": "bob"
    case _: ""

def key_valid(k: String) -> Bool:
  match k:
    case "alice/1": True{}
    case "alice/2": True{}
    case "bob/1": True{}
    case "bob/2": True{}
    case _: False{}

def fields(l: D.Row) -> List<&2, D.Field>:
  D.Row{k, fs} = l
  fs

def Owner(+us: List<&2, D.Row>, name: String, +l: D.Row) -> Data:
  Both<{key_valid(D.row_key(l)) == True{} : Bool},
    Both<{D.find_field(fields(l), "owner") == Some{D.VText{key_owner(D.row_key(l))}} : Maybe<&2, D.Value>},
      {D.exists_row(D.find_row(us, key_owner(D.row_key(l)))) == True{} : Bool}>>

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

def ReadScope(admin: Bool, id: String, +key: String) -> Data:
  match admin:
    case True{}: Unit
    case False{}: Both<{key_owner(key) == id : String}, {key_valid(key) == True{} : Bool}>

def WriteScope(id: String, +key: String) -> Data:
  Both<{key_owner(key) == id : String}, {key_valid(key) == True{} : Bool}>

def Allowed(ctx: D.Context, op: D.Operation) -> Data:
  D.Context{+id, +kind} = ctx
  match op:
    case D.ReadCell{D.Application{name}, k, c}:
      Both<{name == "notes" : String}, ReadScope(String.eq(kind, "admin"), id, k)>
    case D.ViewExistence{D.Application{name}, k}:
      Both<{name == "notes" : String}, ReadScope(String.eq(kind, "admin"), id, k)>
    case D.CountRows{D.Application{name}}:
      Both<{name == "notes" : String}, {kind == "admin" : String}>
    case D.EnumerateKeys{D.Application{name}}:
      Both<{name == "notes" : String}, {kind == "admin" : String}>
    case D.DefineRow{D.Application{name}, +k, fs}:
      Both<{name == "notes" : String}, Both<WriteScope(id, k),
        {D.find_field(fs, "owner") == Some{D.VText{key_owner(k)}} : Maybe<&2, D.Value>}>>
    case D.RemoveRow{D.Application{name}, k}:
      Both<{name == "notes" : String}, WriteScope(id, k)>
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
