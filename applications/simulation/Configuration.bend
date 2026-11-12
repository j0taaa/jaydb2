import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E

type Both<-P: Data, -Q: Data> is Data:
  Both{left: P, right: Q}

# Scenario reads and result writes are restricted to the authenticated row.
def Allowed(ctx: D.Context, op: D.Operation) -> Data:
  D.Context{id, kind} = ctx
  match op:
    case D.ReadCell{D.Application{table}, key, column}:
      Both<{table == "scenarios" : String}, {key == id : String}>
    case D.DefineRow{D.Application{table}, key, fields}:
      Both<{table == "results" : String}, {key == id : String}>
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
  D.Schema{[
    D.SchemaTable{"results", "id", [D.Column{"above", D.Integer{}, False{}},
      D.Column{"id", D.TextValue{}, False{}}, D.Column{"max", D.Integer{}, False{}},
      D.Column{"paths", D.Integer{}, False{}}, D.Column{"sum", D.Integer{}, False{}}]},
    D.SchemaTable{"scenarios", "id", [D.Column{"drift", D.Integer{}, False{}},
      D.Column{"id", D.TextValue{}, False{}}, D.Column{"seed", D.Integer{}, False{}},
      D.Column{"volatility", D.Integer{}, False{}}]}]}

def limits() -> S.Limits:
  S.Limits{65536n, 65536n, 32768n}

def config() -> S.Configuration:
  S.Configuration{schema(), S.MoreOneLaw{Accesses, S.NoneLaw{}}, limits(), E.identity()}
