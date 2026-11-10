# Independent DATA source meaning of an ordered operation list: each primitive
# is evaluated on the working state produced by its predecessor. First failure
# or an observation supplied to the write decoder stops the owned sequence.
# No Action, continuation, trace outcome, or successful-write premise occurs.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

type Plan is Data:
  WriteHandoff{working: D.State,events: List<&2,S.OperationEvent>}
  WriteHalt{working: D.State,events: List<&2,S.OperationEvent>,response: S.Response}

def after(result: D.ResultOp,before: D.State) -> D.State:
  match result:
    case D.Changed{working}: working
    case D.FailureData{}: before
    case D.Observed{observation}: before

def prepend(event: S.OperationEvent,plan: Plan) -> Plan:
  match plan:
    case WriteHandoff{working,events}: WriteHandoff{working,Con{event,events}}
    case WriteHalt{working,events,response}: WriteHalt{working,Con{event,events},response}

def combine(result: D.ResultOp,+before: D.State,+op: D.Operation,tail: Plan) -> Plan:
  match result:
    case D.FailureData{}: WriteHalt{before,[S.OperationEvent{op,S.ErrorOfData{}}],S.Response{S.DataError{},D.VAbsent{}}}
    case D.Observed{observation}: WriteHalt{before,[S.OperationEvent{op,S.Reading{observation}}],S.Response{S.Refusal{},D.VText{"unexpected write return"}}}
    case D.Changed{working}: prepend(S.OperationEvent{op,S.Write{}},tail)

# operations precedes working to make the strict finite-list decrease explicit.
# The tail is source DATA only and discarded at a stop; its events never issue.
def plan(operations: List<&2,D.Operation>,+schema: D.Schema,+before: D.State) -> Plan:
  match operations:
    case Nil{}: WriteHandoff{before,Nil{}}
    case Con{+op,tail}:
      +result = D.operate(schema,before,op)
      combine(result,before,op,plan(tail,schema,after(result,before)))

def depth(operations: List<&2,D.Operation>,remaining: Nat) -> Nat:
  match operations:
    case Nil{}: remaining
    case Con{op,tail}: 1n+depth(tail,remaining)
