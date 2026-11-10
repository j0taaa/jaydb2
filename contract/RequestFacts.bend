# Pure request, termination, decoding and response predicates.
import Base
import ./Logic.bend as L
import ./Data.bend as D
import ./Semantics.bend as S
import ./Protocol.bend as P

def credential(r: P.Request) -> String:
  P.Request{cred, cod, arg, pi} = r
  cred

def code(r: P.Request) -> String:
  P.Request{cred, cod, arg, pi} = r
  cod

def arguments(r: P.Request) -> D.Value:
  P.Request{cred, cod, arg, pi} = r
  arg

def proof(r: P.Request) -> String:
  P.Request{cred, cod, arg, pi} = r
  pi

def Terminates(-p: S.Program, -e: D.Schema, -s: D.State,
  -ctx: D.Context, -args: D.Value) -> Type:
  &n: Nat -> &w: D.State -> &ts: List<&2, S.OperationEvent> -> &r: S.Response ->
    {S.execute(n, p, e, s, ctx, args) == S.Final{w, ts, r} : S.Trace}

def ProgramTerminates(-c: S.Configuration, -p: S.Program) -> Type:
  @s: D.State -> @ctx: D.Context -> @args: D.Value ->
    Terminates(p, S.schema(c), s, ctx, args)

def DecodingCorrect(bs: List<&2, U32>, result: Maybe<&2, D.Value>) -> Type:
  match result:
    case Some{v}:
      P.Decoding(bs, v)
    case None{}:
      @v: D.Value -> P.Decoding(bs, v) -> Empty

def ErrorFixed(r: S.Response) -> Type:
  match r:
    case S.Response{S.Success{}, v}:
      {D.value_valid(v) == True{} : Bool}
    case S.Response{S.Refusal{}, v}:
      {D.value_valid(v) == True{} : Bool}
    case S.Response{s, v}:
      {v == D.VAbsent{} : D.Value}

def AfterOperation(result: D.ResultOp, -state: D.State,
  -operation: D.Operation, -events: List<&2, S.OperationEvent>, -after: S.Trace) -> Type:
  match result:
    case D.FailureData{}:
      {after == S.Final{state,
        S.append(events, S.OperationEvent{operation, S.ErrorOfData{}}),
        S.Response{S.DataError{}, D.VAbsent{}}} : S.Trace}
    case D.Observed{observation}:
      L.E<{S.state_execution_trace(after) == state : D.State},
        {S.events_execution_trace(after) ==
          S.append(events, S.OperationEvent{operation, S.Reading{observation}})
            : List<&2, S.OperationEvent>}>
    case D.Changed{working}:
      L.E<{S.state_execution_trace(after) == working : D.State},
        {S.events_execution_trace(after) ==
          S.append(events, S.OperationEvent{operation, S.Write{}})
            : List<&2, S.OperationEvent>}>
