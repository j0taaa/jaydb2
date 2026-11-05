import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Termination.bend as T
import ./Completion.bend as E
import ./Laws.bend as G
import ./Query.bend as Q
import ./Read.bend as R
import ./Key.bend as K
import ./Bench.bend as B
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as Binding
import ./Interface.bend as F

def depth(qs:List<&2,String>,d:Nat) -> Nat:
  match qs:
    case Nil{}: d
    case Con{q,rest}: Succ{depth(rest,d)}

def indexed(qs:List<&2,String>,+d:Nat,-done:D.Value -> S.Action,h:@v:D.Value -> T.Finite(Succ{d},done(v))) -> T.Finite(depth(qs,Succ{d}),Client.indexed(qs,done)):
  match qs:
    case Nil{}: h(D.VListEmpty{})
    case Con{+q,+rest}: E.reads(["target"],depth(rest,Succ{d}),D.Application{"unique_index"},K.encode([q]),res => Client.indexed(rest,tail => done(D.VList{Client.selected(B.unique_projection(res)),tail})),res => indexed(rest,d,tail => done(D.VList{Client.selected(B.unique_projection(res)),tail}),tail => h(D.VList{Client.selected(B.unique_projection(res)),tail})))

def one(xs:List<&2,String>,+d:Nat,+wanted:String,-done:D.Value -> S.Action,h:@v:D.Value -> T.Finite(Succ{d},done(v))) -> T.Finite(Succ{G.depth(xs,d)},Q.filter_map(~String,~Client.visit,wanted,xs,done)):
  match xs:
    case Nil{}: h(D.VListEmpty{})
    case Con{+key,+rest}: r => one(rest,d,wanted,tail => done(Q.include(Bool.pick(Maybe<&2,D.Value>,B.matches(wanted,r),Some{D.VText{key}},None{}),tail)),tail => h(Q.include(Bool.pick(Maybe<&2,D.Value>,B.matches(wanted,r),Some{D.VText{key}},None{}),tail)))

def scan_depth(+keys:List<&2,String>,qs:List<&2,String>,d:Nat) -> Nat:
  match qs:
    case Nil{}: d
    case Con{q,rest}: G.depth(keys,scan_depth(keys,rest,d))

def scanned(+keys:List<&2,String>,qs:List<&2,String>,+d:Nat,-done:D.Value -> S.Action,h:@v:D.Value -> T.Finite(Succ{d},done(v))) -> T.Finite(Succ{scan_depth(keys,qs,d)},Client.scanned(keys,qs,done)):
  match qs:
    case Nil{}: h(D.VListEmpty{})
    case Con{+q,+rest}: one(keys,scan_depth(keys,rest,d),q,item => Client.scanned(keys,rest,tail => done(D.VList{item,tail})),item => scanned(keys,rest,d,tail => done(D.VList{item,tail}),tail => h(D.VList{item,tail})))

def keys(+qs:List<&2,String>,r:S.Return,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> E.Complete(R.keys_return(keys => Client.scanned(keys,qs,v => S.Finish{v}),r),e,s,ts):
  match r:
    case S.Datum{D.Keys{+xs}}: E.finite(Succ{scan_depth(xs,qs,0n)},Client.scanned(xs,qs,v => S.Finish{v}),e,s,ts,scanned(xs,qs,0n,v => S.Finish{v},v => Unit{}))
    case S.Datum{D.RowAbsent{}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Cell{v}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Existence{v}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Count{v}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.UnitValue{}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})

def choose(mode:Bool,+qs:List<&2,String>,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> E.Complete(Client.choose(mode,qs),e,s,ts):
  match mode:
    case True{}: E.finite(depth(qs,1n),Client.indexed(qs,v => S.Finish{v}),e,s,ts,indexed(qs,0n,v => S.Finish{v},v => Unit{}))
    case False{}: E.access(D.EnumerateKeys{D.Application{"base"}},R.keys_return(keys => Client.scanned(keys,qs,v => S.Finish{v})),e,s,ts,r => w => events => keys(qs,r,e,w,events))

def command(c:Client.Command,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> E.Complete(Client.command(c),e,s,ts):
  match c:
    case Client.Batch{mode,qs}: choose(mode,qs,e,s,ts)
    case Client.Invalid{}: E.finite(1n,S.Refuse{D.VAbsent{}},e,s,ts,Unit{})

def complete(args:D.Value,e:D.Schema,s:D.State,ts:List<&2,S.OperationEvent>) -> E.Complete(Client.start(args),e,s,ts):
  command(Client.parse(args),e,s,ts)

def Binding.certificate(ctx,args,s,valid,identity,n):
  L.execution_trace_free_covers_prefixes_and_final(S.execute(n,Client.program(),C.schema(),s,ctx,args),C.schema(),C.limits(),S.environment(I.config()),s,ctx,Binding.code(),args)

def terminate(+s:D.State,+ctx:D.Context,+args:D.Value,h:E.Complete(S.start(Client.program(),ctx,args),C.schema(),s,Nil{})) -> F.Terminates(Client.program(),C.schema(),s,ctx,args):
  match h:
    case (n,w,events,r,eq): T.witness_program(n,Client.program(),C.schema(),s,ctx,args,(w,events,r,eq))

def Binding.terminates(s,ctx,args):
  +state=s
  +context=ctx
  +arguments=args
  terminate(state,context,arguments,complete(arguments,C.schema(),state,Nil{}))
