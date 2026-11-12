# Termination with a bound that may depend on the actual observation
# (adapted from applications/indexed/Completion.bend). No host quota is used.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Termination.bend as T

# Unlike Finite, the bound may depend on the actual observed return/state.
def Complete(-a:S.Action,-e:D.Schema,-s:D.State,-ts:List<&2,S.OperationEvent>) -> Type:
  &n:Nat -> T.End(n,a,e,s,ts)

def finite(+n:Nat,a:S.Action,e:D.Schema,s:D.State,ts:List<&2,S.OperationEvent>,h:T.Finite(n,a)) -> Complete(a,e,s,ts):
  (n,T.finite_terminates(n,a,e,s,ts,h))

def Resumes(-step:S.Step,-e:D.Schema,-ts:List<&2,S.OperationEvent>) -> Type:
  &n:Nat -> &w:D.State -> &events:List<&2,S.OperationEvent> -> &r:S.Response ->
    {S.resume_execution_trace(n,step,e,ts) == S.Final{w,events,r} : S.Trace}

def continued(+s:D.State,-a:S.Action,+ev:S.OperationEvent,+e:D.Schema,+ts:List<&2,S.OperationEvent>,h:Complete(a,e,s,S.append(ts,ev))) ->
  Resumes(S.Continue{s,a,ev},e,ts):
  match h:
    case (+n,+w,+events,+r,eq):
      (n,w,events,r,Equal.trans(S.Trace,S.resume_execution_trace(n,S.Continue{s,a,ev},e,ts),T.observe(n,a,e,s,S.append(ts,ev)),S.Final{w,events,r},T.continuation(n,s,a,ev,e,ts),eq))

def result(res:D.ResultOp,+op:D.Operation,-k:S.Return -> S.Action,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,
  next:@r:S.Return -> @w:D.State -> @events:List<&2,S.OperationEvent> -> Complete(k(r),e,w,events)) -> Resumes(S.apply(res,s,op,k),e,ts):
  match res:
    case D.FailureData{}:
      (0n,s,S.append(ts,S.OperationEvent{op,S.ErrorOfData{}}),S.response_error(S.DataError{}),T.failure_of_operation(0n,s,S.OperationEvent{op,S.ErrorOfData{}},e,ts))
    case D.Observed{+obs}:
      continued(s,k(S.Datum{obs}),S.OperationEvent{op,S.Reading{obs}},e,ts,next(S.Datum{obs},s,S.append(ts,S.OperationEvent{op,S.Reading{obs}})))
    case D.Changed{+w}:
      continued(w,k(S.UnitValue{}),S.OperationEvent{op,S.Write{}},e,ts,next(S.UnitValue{},w,S.append(ts,S.OperationEvent{op,S.Write{}})))

def lift(+op:D.Operation,-k:S.Return -> S.Action,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,h:Resumes(S.step(S.Access{op,k},e,s),e,ts)) -> Complete(S.Access{op,k},e,s,ts):
  match h:
    case (n,w,events,r,eq): (Succ{n},w,events,r,eq)

def access(+op:D.Operation,-k:S.Return -> S.Action,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,
  next:@r:S.Return -> @w:D.State -> @events:List<&2,S.OperationEvent> -> Complete(k(r),e,w,events)) -> Complete(S.Access{op,k},e,s,ts):
  lift(op,k,e,s,ts,result(D.operate(e,s,op),op,k,e,s,ts,next))
