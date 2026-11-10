# Independent visitor DATA model: original key order, concatenated local
# operations, and ordered Some payload projection. No Action appears here.
import Base
import ./ReadPrefixComposition.bend as C
import ../contract/Data.bend as D
import ./Sequence.bend as Sequence
import ./Query.bend as Query

def budget(~Env: Data,~cost: Env -> String -> Nat -> Nat,+env: Env,keys: List<&2,String>,+index: Nat) -> Nat:
  match keys:
    case Nil{}: 0n
    case Con{+key,tail}: Nat.add(cost(env,key,index),budget(~Env,~cost,env,tail,Nat.add(cost(env,key,index),index)))

def operations(~Env: Data,~cost: Env -> String -> Nat -> Nat,~ops: Env -> String -> Nat -> List<&2,D.Operation>,+env: Env,keys: List<&2,String>,+index: Nat) -> List<&2,D.Operation>:
  match keys:
    case Nil{}: Nil{}
    case Con{+key,tail}: C.append(ops(env,key,index),operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index)))

def push(item: Maybe<&2,D.Value>,tail: List<&2,D.Value>) -> List<&2,D.Value>:
  match item:
    case None{}: tail
    case Some{value}: Con{value,tail}

def items(~Env: Data,~cost: Env -> String -> Nat -> Nat,~item: Env -> String -> Nat -> Maybe<&2,D.Value>,+env: Env,keys: List<&2,String>,+index: Nat) -> List<&2,D.Value>:
  match keys:
    case Nil{}: Nil{}
    case Con{+key,tail}: push(item(env,key,index),items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))

law projected_items_encode_exactly_the_query_include_operation:
  for +item: Maybe<&2,D.Value>
  for +tail: List<&2,D.Value>
  {Sequence.values(push(item,tail)) == Query.include(item,Sequence.values(tail)) : D.Value}
def projected_items_encode_exactly_the_query_include_operation(item,tail):
  match item:
    case None{}: {==}
    case Some{value}: {==}
