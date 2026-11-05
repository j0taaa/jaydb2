import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Model.bend as M
import ./TableLaws.bend as TL

type Both<-P:Data,-Q:Data> is Data:
  Both{left:P,right:Q}

def Scope(+id:String,c:D.Collection) -> Data:
  match c:
    case D.Application{name}: {String.eq(name,id) || String.eq(name,id ++ "_index") == True{} : Bool}
    case D.Users{}: Empty

def Allowed(ctx:D.Context,op:D.Operation) -> Data:
  D.Context{+id,kind}=ctx
  Scope(id,D.collection_op(op))

def AllAllowed(+ctx:D.Context,ts:List<&2,S.OperationEvent>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{S.OperationEvent{op,ef},rest}: Both<Allowed(ctx,op),AllAllowed(ctx,rest)>

def Rule(h:S.Situation) -> Data:
  match h:
    case S.Stable{s}: M.Layout(s)
    case S.Executing{s,ctx,code,args,w,ts}: Both<M.Layout(w),AllAllowed(ctx,ts)>
    case S.Closed{s,ctx,code,args,w,ts,r}: Both<M.Layout(w),AllAllowed(ctx,ts)>

def IndexInvariant(s:D.State) -> Type:
  M.Indexes(s)

def IndexRule(h:S.Situation) -> Type:
  TL.OnStable(~IndexInvariant,h)

def laws() -> S.Laws:
  S.MoreOneLaw{Rule,S.MoreOneLaw{IndexRule,S.NoneLaw{}}}
