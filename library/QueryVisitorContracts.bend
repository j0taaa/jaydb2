# Necessary LOCAL component refinements for arbitrary visitors. Each call's
# certificate concerns one original key/start index and ANY continuation/depth.
# A finite spine consumes each proof once; no arbitrary Type is copied, and
# neither a completed map outcome nor a whole desired trace is a premise.
import Base
import ./ReadPrefix.bend as Cut
import ./ReadPrefixComposition.bend as C
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L

def Local(~Env: Data,~visit: Env -> String -> (Maybe<&2,D.Value> -> S.Action) -> S.Action,~reply: Env -> Nat -> S.Return,~cost: Env -> String -> Nat -> Nat,~ops: Env -> String -> Nat -> List<&2,D.Operation>,~item: Env -> String -> Nat -> Maybe<&2,D.Value>,+env: Env,+key: String,+index: Nat) -> Type:
  @+remaining: Nat -> @-done: (Maybe<&2,D.Value> -> S.Action) -> {Cut.cut(~Env,~reply,env,Nat.add(cost(env,key,index),remaining),index,visit(env,key,done)) == C.attach(ops(env,key,index),Cut.cut(~Env,~reply,env,remaining,Nat.add(cost(env,key,index),index),done(item(env,key,index)))) : Cut.Prefix}

def Calls(~Env: Data,~visit: Env -> String -> (Maybe<&2,D.Value> -> S.Action) -> S.Action,~reply: Env -> Nat -> S.Return,~cost: Env -> String -> Nat -> Nat,~ops: Env -> String -> Nat -> List<&2,D.Operation>,~item: Env -> String -> Nat -> Maybe<&2,D.Value>,+env: Env,keys: List<&2,String>,+index: Nat) -> Type:
  match keys:
    case Nil{}: Unit
    case Con{+key,tail}: L.E<Local(~Env,~visit,~reply,~cost,~ops,~item,env,key,index),Calls(~Env,~visit,~reply,~cost,~ops,~item,env,tail,Nat.add(cost(env,key,index),index))>
