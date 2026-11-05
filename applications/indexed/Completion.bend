import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Termination.bend as T
import ./Action.bend as A
import ./Mutation.bend as M
import ./Query.bend as Q
import ./Read.bend as R
import ./Index.bend as X
import ./Laws.bend as G
import ./Key.bend as K

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

def written(d:Nat,-a:S.Action,h:T.Finite(d,a),r:S.Return) -> T.Finite(d,A.written(a,r)):
  match d r:
    case Zero{} r: h
    case Succ{m} S.UnitValue{}: h
    case Succ{m} S.Datum{obs}: Unit{}

def removes(xs:List<&2,String>,+d:Nat,+c:D.Collection,-done:S.Action,h:T.Finite(d,done)) ->
  T.Finite(G.depth(xs,d),M.remove_rows(c,xs,done)):
  match xs:
    case Nil{}: h
    case Con{key,+rest}: r => written(G.depth(rest,d),M.remove_rows(c,rest,done),removes(rest,d,c,done,h),r)

def reads(xs:List<&2,String>,+d:Nat,+c:D.Collection,+key:String,-done:Q.Selection -> S.Action,h:@res:Q.Selection -> T.Finite(d,done(res))) ->
  T.Finite(G.depth(xs,d),Q.read_fields(c,key,xs,done)):
  match xs:
    case Nil{}: h(Q.Selected{D.VRecordEmpty{}})
    case Con{+name,+rest}: +r => reads(rest,d,c,key,res => done(Q.combine(name,r,res)),res => h(Q.combine(name,r,res)))

def projected(d:Nat,+value:String,-done:Maybe<&2,D.Value> -> S.Action,h:@item:Maybe<&2,D.Value> -> T.Finite(d,done(item)),p:X.Projection) -> T.Finite(d,X.projected(value,done,p)):
  match d:
    case Zero{}: h(None{})
    case Succ{m}:
      match p:
        case X.Target{target,v}: h(Bool.pick(Maybe<&2,D.Value>,String.eq(value,v),Some{D.VText{target}},None{}))
        case X.Missing{}: h(None{})
        case X.Invalid{}: Unit{}

def scan_depth(xs:List<&2,String>,n:Nat) -> Nat:
  match xs:
    case Nil{}: Succ{n}
    case Con{x,rest}: Succ{Succ{scan_depth(rest,n)}}

def scan(xs:List<&2,String>,+n:Nat,+env:X.Scan,-done:D.Value -> S.Action,h:@out:D.Value -> T.Finite(Succ{n},done(out))) ->
  T.Finite(scan_depth(xs,n),Q.filter_map(~X.Scan,~X.visit,env,xs,done)):
  match xs env:
    case Nil{} env: h(D.VListEmpty{})
    case Con{key,+rest} X.Scan{+c,+value}:
      reads(["target","value"],scan_depth(rest,n),c,key,X.selected(value,+item => Q.filter_map(~X.Scan,~X.visit,X.Scan{c,value},rest,tail => done(Q.include(item,tail)))),
        res => projected(scan_depth(rest,n),value,+item => Q.filter_map(~X.Scan,~X.visit,X.Scan{c,value},rest,tail => done(Q.include(item,tail))),
          item => scan(rest,n,X.Scan{c,value},tail => done(Q.include(item,tail)),tail => h(Q.include(item,tail))),X.projection(res)))

def writes(xs:List<&2,D.Row>,+d:Nat,+c:D.Collection,-done:S.Action,h:T.Finite(d,done)) ->
  T.Finite(G.row_depth(xs,d),A.define_rows(c,xs,done)):
  match xs:
    case Nil{}: h
    case Con{D.Row{key,fs},+rest}: r => written(G.row_depth(rest,d),A.define_rows(c,rest,done),writes(rest,d,c,done,h),r)

def rebuild_return(+c:D.Collection,+row:D.Row,r:S.Return,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) ->
  Complete(R.keys_return(keys => M.remove_rows(c,keys,A.define_rows(c,[row],S.Finish{D.VText{"rebuilt"}})),r),e,s,ts):
  match r:
    case S.Datum{D.Keys{+keys}}:
      finite(G.depth(keys,2n),M.remove_rows(c,keys,A.define_rows(c,[row],S.Finish{D.VText{"rebuilt"}})),e,s,ts,
        removes(keys,2n,c,A.define_rows(c,[row],S.Finish{D.VText{"rebuilt"}}),writes([row],1n,c,S.Finish{D.VText{"rebuilt"}},Unit{})))
    case S.Datum{D.RowAbsent{}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Cell{v}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Existence{b}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Count{n}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.UnitValue{}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})

def rebuild(+c:D.Collection,+row:D.Row,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> Complete(X.rebuild(c,[row],S.Finish{D.VText{"rebuilt"}}),e,s,ts):
  access(D.EnumerateKeys{c},R.keys_return(keys => M.remove_rows(c,keys,A.define_rows(c,[row],S.Finish{D.VText{"rebuilt"}}))),e,s,ts,
    r => w => events => rebuild_return(c,row,r,e,w,events))

def lookup_return(+c:D.Collection,+value:String,r:S.Return,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) ->
  Complete(R.keys_return(keys => Q.filter_map(~X.Scan,~X.visit,X.Scan{c,value},keys,v => S.Finish{v}),r),e,s,ts):
  match r:
    case S.Datum{D.Keys{+keys}}:
      finite(scan_depth(keys,0n),Q.filter_map(~X.Scan,~X.visit,X.Scan{c,value},keys,v => S.Finish{v}),e,s,ts,scan(keys,0n,X.Scan{c,value},v => S.Finish{v},v => Unit{}))
    case S.Datum{D.RowAbsent{}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Cell{v}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Existence{b}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Count{n}}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.UnitValue{}: finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})

def lookup(+c:D.Collection,parts:List<&2,String>,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> Complete(X.lookup_many(c,parts,v => S.Finish{v}),e,s,ts):
  +value=K.encode(parts)
  access(D.EnumerateKeys{c},R.keys_return(keys => Q.filter_map(~X.Scan,~X.visit,X.Scan{c,value},keys,v => S.Finish{v})),e,s,ts,
    r => w => events => lookup_return(c,value,r,e,w,events))
