# Links between REAL program operations and their semantic prefixes.
# Instants are positions in environment semantics, not physical times.
# A snapshot does not require a log stored by the server.
import Base
import ./Logic.bend as L
import ./Data.bend as D
import ./Protocol.bend as P
import ./Semantics.bend as S
import ./Interface.bend as I

# A concluded call cannot resume executing requester code.
def WithoutConclusionPrevious(-a: I.Environment, -k: String, -x: I.Scenario,
  -t: Nat) -> Type:
  @response: S.Response -> @published: D.State -> @closes: Bool ->
    I.Before(a, k, x, t, I.Concluded{response, published, closes}) -> Empty

# A Final path is terminal even before preparing/delivering the response.
def PrefixesNotTerminated(-a: I.Environment, -k: String, -x: I.Scenario,
  -t: Nat) -> Type:
  @req: P.Request -> @ctx: D.Context -> @program: S.Program ->
    @working: D.State -> @events: List<&2, S.OperationEvent> -> @response: S.Response ->
      I.Before(a, k, x, t,
        I.Evaluated{req, ctx, program, S.Final{working, events, response}}) -> Empty

def ObservationWindow(-before: Nat, -operation: Nat, -later: Nat) -> Type:
  L.E<{Nat.is_lt(before, operation) == True{} : Bool},
    {Nat.is_lt(operation, later) == True{} : Bool}>

# Besides linking each operation to an event, this prevents two distinct real
# operations from using the same transition of one event as proof.
def UniqueOperationInWindow(-a: I.Environment, -k: String, -x: I.Scenario,
  -before: Nat, -later: Nat, -t: Nat, -schema: D.Schema,
  -state: D.State, -operation: D.Operation, -result: D.ResultOp) -> Type:
  @u: Nat -> @e2: D.Schema -> @s2: D.State ->
    @o2: D.Operation -> @r2: D.ResultOp ->
      {Nat.is_lt(before, u) == True{} : Bool} ->
      {Nat.is_lt(u, later) == True{} : Bool} ->
      I.Happens(a, k, x, u, I.Operated{e2, s2, o2, r2}) ->
        L.E<{u == t : Nat},
          {I.Operated{e2, s2, o2, r2} ==
            I.Operated{schema, state, operation, result} : I.Fact}>

# The event does not hide absence, errors or writes without effect.
# A write result does not appear as an observation of the previous state.
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

def OperationBound(-a: I.Environment, -k: String, -x: I.Scenario,
  -t: Nat, -schema: D.Schema, -state: D.State,
  -operation: D.Operation, -result: D.ResultOp) -> Type:
  &req: P.Request -> &ctx: D.Context -> &program: S.Program ->
    &events: List<&2, S.OperationEvent> -> &before: Nat -> &later: Nat ->
      &after: S.Trace ->
        L.E<{schema == S.schema(I.configuration(x)) : D.Schema},
          L.E<ObservationWindow(before, t, later),
            L.E<I.Happens(a, k, x, before,
              I.Evaluated{req, ctx, program, S.Prefix{state, events}}),
              L.E<I.Happens(a, k, x, later,
                I.Evaluated{req, ctx, program, after}),
                L.E<AfterOperation(result, state, operation, events, after),
                  UniqueOperationInWindow(a, k, x, before, later, t,
                    schema, state, operation, result)>>>>>
