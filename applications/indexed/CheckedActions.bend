# Actual-operation weakest preconditions. A certificate must establish every
# transition and the terminal exact projection; no final-state guard/certificate.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Termination.bend as T
import ./ValidationFinal.bend as V
import ./Policy.bend as P
import ./Model.bend as M

# The post is proved on the REAL operation result, not a guessed certificate.
def Step(res:D.ResultOp,+s:D.State,post:@r:S.Return -> @w:D.State -> Type) -> Type:
  match res:
    case D.FailureData{}: M.Indexes(s)
    case D.Observed{obs}: post(S.Datum{obs},s)
    case D.Changed{+w}: L.E<M.Layout(w),post(S.UnitValue{},w)>

def Safe(d:Nat,+e:D.Schema,+ctx:D.Context,+s:D.State,a:S.Action) -> Type:
  match d:
    case Zero{}: Empty
    case Succ{m}:
      match a:
        case S.Finish{v}: M.Indexes(s)
        case S.Refuse{v}: M.Indexes(s)
        case S.Access{+op,k}:
          L.E<P.Allowed(ctx,op),Step(D.operate(e,s,op),s,r => w => Safe(m,e,ctx,w,k(r)))>

def Good(+ctx:D.Context,+s:D.State,ts:List<&2,S.OperationEvent>) -> Data:
  P.Both<M.Layout(s),P.AllAllowed(ctx,ts)>

def Terminal(p:S.Trace) -> Data:
  match p:
    case S.Prefix{w,ts}: Unit
    case S.Final{+w,ts,r}: M.Coherent(w)

def Path(+ctx:D.Context,+p:S.Trace) -> Data:
  P.Both<Good(ctx,S.state_execution_trace(p),S.events_execution_trace(p)),Terminal(p)>

def rewind(-ctx:D.Context,-a:S.Trace,-b:S.Trace,eq:{a == b : S.Trace},h:Path(ctx,b)) -> Path(ctx,a):
  %Equal.sym(S.Trace,a,b,eq) : Path(ctx,_)
  h

def append(+ctx:D.Context,ts:List<&2,S.OperationEvent>,+op:D.Operation,+ef:S.Effect,h:P.AllAllowed(ctx,ts),p:P.Allowed(ctx,op)) ->
  P.AllAllowed(ctx,S.append(ts,S.OperationEvent{op,ef})):
  match ts h:
    case Nil{} Unit{}: P.Both{p,Unit{}}
    case Con{S.OperationEvent{o,f},rest} P.Both{hp,ht}: P.Both{hp,append(ctx,rest,op,ef,ht,p)}

def good_layout(-ctx:D.Context,-s:D.State,-ts:List<&2,S.OperationEvent>,good:Good(ctx,s,ts)) -> M.Layout(s):
  P.Both{layout,hist}=good
  layout

def result(res:D.ResultOp,+d:Nat,+n:Nat,+ctx:D.Context,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,+op:D.Operation,-k:S.Return -> S.Action,
  +good:Good(ctx,s,ts),p:P.Allowed(ctx,op),h:Step(res,s,r => w => Safe(d,e,ctx,w,k(r))),
  rec:@r:S.Return -> @w:D.State -> @events:List<&2,S.OperationEvent> -> Good(ctx,w,events) -> Safe(d,e,ctx,w,k(r)) -> Path(ctx,T.observe(n,k(r),e,w,events))) ->
  Path(ctx,S.resume_execution_trace(n,S.apply(res,s,op,k),e,ts)):
  match res:
    case D.FailureData{}:
      P.Both{+layout,hist}=good
      rewind(ctx,S.resume_execution_trace(n,S.OperationFailed{s,S.OperationEvent{op,S.ErrorOfData{}}},e,ts),
        S.Final{s,S.append(ts,S.OperationEvent{op,S.ErrorOfData{}}),S.response_error(S.DataError{})},T.failure_of_operation(n,s,S.OperationEvent{op,S.ErrorOfData{}},e,ts),
        P.Both{P.Both{layout,append(ctx,ts,op,S.ErrorOfData{},hist,p)},M.canonical(s,layout,h)})
    case D.Observed{+obs}:
      P.Both{+layout,hist}=good
      rewind(ctx,S.resume_execution_trace(n,S.Continue{s,k(S.Datum{obs}),S.OperationEvent{op,S.Reading{obs}}},e,ts),
        T.observe(n,k(S.Datum{obs}),e,s,S.append(ts,S.OperationEvent{op,S.Reading{obs}})),T.continuation(n,s,k(S.Datum{obs}),S.OperationEvent{op,S.Reading{obs}},e,ts),
        rec(S.Datum{obs},s,S.append(ts,S.OperationEvent{op,S.Reading{obs}}),P.Both{layout,append(ctx,ts,op,S.Reading{obs},hist,p)},h))
    case D.Changed{+w}:
      P.Both{+layout,hist}=good
      L.Both{next,tail}=h
      rewind(ctx,S.resume_execution_trace(n,S.Continue{w,k(S.UnitValue{}),S.OperationEvent{op,S.Write{}}},e,ts),
        T.observe(n,k(S.UnitValue{}),e,w,S.append(ts,S.OperationEvent{op,S.Write{}})),T.continuation(n,w,k(S.UnitValue{}),S.OperationEvent{op,S.Write{}},e,ts),
        rec(S.UnitValue{},w,S.append(ts,S.OperationEvent{op,S.Write{}}),P.Both{next,append(ctx,ts,op,S.Write{},hist,p)},tail))

def safe(d:Nat,+n:Nat,a:S.Action,+ctx:D.Context,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,h:Safe(d,e,ctx,s,a),+good:Good(ctx,s,ts)) ->
  Path(ctx,T.observe(n,a,e,s,ts)):
  match d h:
    case Zero{} h: L.ex_false(Path(ctx,T.observe(n,a,e,s,ts)),h)
    case Succ{+m} h:
      match n:
        case Zero{}: P.Both{good,Unit{}}
        case Succ{rest}:
          match a h:
            case S.Finish{v} exact:
              rewind(ctx,S.resume_execution_trace(rest,S.Stopped{s,S.Response{S.Success{},v}},e,ts),S.Final{s,ts,S.Response{S.Success{},v}},T.stopped(rest,s,S.Response{S.Success{},v},e,ts),P.Both{good,M.canonical(s,good_layout(ctx,s,ts,good),exact)})
            case S.Refuse{v} exact:
              rewind(ctx,S.resume_execution_trace(rest,S.Stopped{s,S.Response{S.Refusal{},v}},e,ts),S.Final{s,ts,S.Response{S.Refusal{},v}},T.stopped(rest,s,S.Response{S.Refusal{},v},e,ts),P.Both{good,M.canonical(s,good_layout(ctx,s,ts,good),exact)})
            case S.Access{+op,k} L.Both{p,step}:
              result(D.operate(e,s,op),m,rest,ctx,e,s,ts,op,k,good,p,step,
                +r => w => events => g => h => safe(m,rest,k(r),ctx,e,w,events,h,g))

def configuration(e:D.Schema,lim:S.Limits,amb:String) -> S.Configuration:
  S.Configuration{e,P.laws(),lim,amb}

def prefix(-e:D.Schema,-lim:S.Limits,-amb:String,-s:D.State,-ctx:D.Context,-code:String,-args:D.Value,-w:D.State,-ts:List<&2,S.OperationEvent>,+good:Good(ctx,w,ts)) ->
  R.SafetyPrefix(configuration(e,lim,amb),s,ctx,code,args,w,ts):
  L.Both{L.Both{good,L.Both{Unit{},Unit{}}},L.Both{good,L.Both{Unit{},Unit{}}}}

def closed_index(r:S.Response,+w:D.State,exact:M.Coherent(w),-initial:D.State,-ctx:D.Context,-code:String,-args:D.Value,-ts:List<&2,S.OperationEvent>) ->
  P.IndexRule(S.Closed{initial,ctx,code,args,w,ts,r}):
  match r:
    case S.Response{S.Success{},v}: M.coherent_indexes(w,exact)
    case S.Response{S.Refusal{},v}: Unit{}
    case S.Response{S.Input{},v}: Unit{}
    case S.Response{S.Authentication{},v}: Unit{}
    case S.Response{S.Certificate{},v}: Unit{}
    case S.Response{S.DataError{},v}: Unit{}
    case S.Response{S.Limit{},v}: Unit{}
    case S.Response{S.Failure{},v}: Unit{}

def finalize(r:S.Response,+e:D.Schema,+lim:S.Limits,+amb:String,+w:D.State,+exact:M.Coherent(w)) ->
  R.PublicationValid(R.finalize(r,configuration(e,lim,amb),w),configuration(e,lim,amb),w):
  match r:
    case S.Response{S.Success{},+v}:
      V.state_validated(D.structure(e,w),R.fits(R.limit_state(lim),D.state_value(w)),e,P.laws(),lim,amb,w,v,D.value_valid(v),
        R.fits(R.limit_response(lim),S.response_value(S.Response{S.Success{},v})),{==},{==},
        L.Both{M.coherent_layout(w,exact),L.Both{M.coherent_indexes(w,exact),Unit{}}})
    case S.Response{S.Refusal{},+v}:
      V.refusal_validated(D.value_valid(v),R.fits(R.limit_response(lim),S.response_value(S.Response{S.Refusal{},v})),configuration(e,lim,amb),w,v)
    case S.Response{S.Input{},v}: Unit{}
    case S.Response{S.Authentication{},v}: Unit{}
    case S.Response{S.Certificate{},v}: Unit{}
    case S.Response{S.DataError{},v}: Unit{}
    case S.Response{S.Limit{},v}: Unit{}
    case S.Response{S.Failure{},v}: Unit{}

def execution_trace(p:S.Trace,+e:D.Schema,+lim:S.Limits,+amb:String,-s:D.State,-ctx:D.Context,-code:String,-args:D.Value,h:Path(ctx,p)) ->
  R.SafetyTrace(p,configuration(e,lim,amb),s,ctx,code,args):
  match p h:
    case S.Prefix{w,ts} P.Both{good,Unit{}}: prefix(e,lim,amb,s,ctx,code,args,w,ts,good)
    case S.Final{+w,ts,+r} P.Both{+good,+exact}:
      L.Both{prefix(e,lim,amb,s,ctx,code,args,w,ts,good),
        L.Both{L.Both{good,L.Both{closed_index(R.finalize(r,configuration(e,lim,amb),w),w,exact,s,ctx,code,args,ts),Unit{}}},finalize(r,e,lim,amb,w,exact)}}

# A separate permission-only judgment used by the audit's negative controls.
# It checks the same actual operations at every step but does not assume any
# index postcondition. Omitted/forged variants must prove this before their
# full certificate is tested and rejected at the exact-index obligation.
def PermittedStep(res:D.ResultOp,+s:D.State,post:@r:S.Return -> @w:D.State -> Type) -> Type:
  match res:
    case D.FailureData{}: Unit
    case D.Observed{obs}: post(S.Datum{obs},s)
    case D.Changed{w}: post(S.UnitValue{},w)

def Permissions(d:Nat,+e:D.Schema,+ctx:D.Context,+s:D.State,a:S.Action) -> Type:
  match d:
    case Zero{}: Empty
    case Succ{m}:
      match a:
        case S.Finish{v}: Unit
        case S.Refuse{v}: Unit
        case S.Access{+op,k}: L.E<P.Allowed(ctx,op),PermittedStep(D.operate(e,s,op),s,r => w => Permissions(m,e,ctx,w,k(r)))>

# Soundness of permission-only negative controls for ALL execution prefixes.
def allowed_rewind(-ctx:D.Context,-a:S.Trace,-b:S.Trace,eq:{a == b : S.Trace},h:P.AllAllowed(ctx,S.events_execution_trace(b))) -> P.AllAllowed(ctx,S.events_execution_trace(a)):
  %Equal.sym(S.Trace,a,b,eq) : P.AllAllowed(ctx,S.events_execution_trace(_))
  h

def permitted_result(res:D.ResultOp,+d:Nat,+n:Nat,+ctx:D.Context,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,+op:D.Operation,-k:S.Return -> S.Action,
  hist:P.AllAllowed(ctx,ts),p:P.Allowed(ctx,op),h:PermittedStep(res,s,r => w => Permissions(d,e,ctx,w,k(r))),
  rec:@r:S.Return -> @w:D.State -> @events:List<&2,S.OperationEvent> -> P.AllAllowed(ctx,events) -> Permissions(d,e,ctx,w,k(r)) -> P.AllAllowed(ctx,S.events_execution_trace(T.observe(n,k(r),e,w,events)))) ->
  P.AllAllowed(ctx,S.events_execution_trace(S.resume_execution_trace(n,S.apply(res,s,op,k),e,ts))):
  match res:
    case D.FailureData{}:
      allowed_rewind(ctx,S.resume_execution_trace(n,S.OperationFailed{s,S.OperationEvent{op,S.ErrorOfData{}}},e,ts),S.Final{s,S.append(ts,S.OperationEvent{op,S.ErrorOfData{}}),S.response_error(S.DataError{})},T.failure_of_operation(n,s,S.OperationEvent{op,S.ErrorOfData{}},e,ts),append(ctx,ts,op,S.ErrorOfData{},hist,p))
    case D.Observed{+obs}:
      allowed_rewind(ctx,S.resume_execution_trace(n,S.Continue{s,k(S.Datum{obs}),S.OperationEvent{op,S.Reading{obs}}},e,ts),T.observe(n,k(S.Datum{obs}),e,s,S.append(ts,S.OperationEvent{op,S.Reading{obs}})),T.continuation(n,s,k(S.Datum{obs}),S.OperationEvent{op,S.Reading{obs}},e,ts),
        rec(S.Datum{obs},s,S.append(ts,S.OperationEvent{op,S.Reading{obs}}),append(ctx,ts,op,S.Reading{obs},hist,p),h))
    case D.Changed{+w}:
      allowed_rewind(ctx,S.resume_execution_trace(n,S.Continue{w,k(S.UnitValue{}),S.OperationEvent{op,S.Write{}}},e,ts),T.observe(n,k(S.UnitValue{}),e,w,S.append(ts,S.OperationEvent{op,S.Write{}})),T.continuation(n,w,k(S.UnitValue{}),S.OperationEvent{op,S.Write{}},e,ts),
        rec(S.UnitValue{},w,S.append(ts,S.OperationEvent{op,S.Write{}}),append(ctx,ts,op,S.Write{},hist,p),h))

def permissions_trace(d:Nat,+n:Nat,a:S.Action,+ctx:D.Context,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,h:Permissions(d,e,ctx,s,a),hist:P.AllAllowed(ctx,ts)) ->
  P.AllAllowed(ctx,S.events_execution_trace(T.observe(n,a,e,s,ts))):
  match d h:
    case Zero{} h: L.ex_false(P.AllAllowed(ctx,S.events_execution_trace(T.observe(n,a,e,s,ts))),h)
    case Succ{+m} h:
      match n:
        case Zero{}: hist
        case Succ{rest}:
          match a h:
            case S.Finish{v} Unit{}:
              allowed_rewind(ctx,S.resume_execution_trace(rest,S.Stopped{s,S.Response{S.Success{},v}},e,ts),S.Final{s,ts,S.Response{S.Success{},v}},T.stopped(rest,s,S.Response{S.Success{},v},e,ts),hist)
            case S.Refuse{v} Unit{}:
              allowed_rewind(ctx,S.resume_execution_trace(rest,S.Stopped{s,S.Response{S.Refusal{},v}},e,ts),S.Final{s,ts,S.Response{S.Refusal{},v}},T.stopped(rest,s,S.Response{S.Refusal{},v},e,ts),hist)
            case S.Access{+op,k} L.Both{p,step}:
              permitted_result(D.operate(e,s,op),m,rest,ctx,e,s,ts,op,k,hist,p,step,
                +r => w => events => h => p => permissions_trace(m,rest,k(r),ctx,e,w,events,p,h))
