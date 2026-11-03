import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E

type Both<-P: Data, -Q: Data> is Data:
  Both{left: P, right: Q}

# Every read and write requires the authenticated ID and authorized column.
def Allowed(ctx: D.Context, op: D.Operation) -> Data:
  D.Context{id, kind} = ctx
  match op:
    case D.ReadCell{D.Users{}, key, column}:
      Both<{key == id : String}, {column == "credential" : String}>
    case D.DefineColumn{D.Users{}, key, column, value}:
      Both<{key == id : String}, {column == "credential" : String}>
    case _:
      {False{} == True{} : Bool}

def AllAllowed(ctx: D.Context, ts: List<&2, S.OperationEvent>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{S.OperationEvent{op, effect}, rest}: Both<Allowed(ctx, op), AllAllowed(ctx, rest)>

def Accesses(h: S.Situation) -> Data:
  match h:
    case S.Stable{s}: Unit
    case S.Executing{s, ctx, code, args, w, ts}: AllAllowed(ctx, ts)
    case S.Closed{s, ctx, code, args, w, ts, response}: AllAllowed(ctx, ts)

def schema() -> D.Schema:
  D.Schema{Nil{}}

def limits() -> S.Limits:
  S.Limits{32768n, 65536n, 32768n}

def config() -> S.Configuration:
  S.Configuration{schema(), S.MoreOneLaw{Accesses, S.NoneLaw{}}, limits(), E.identity()}
