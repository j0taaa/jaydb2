# Independent source-index meaning of the ordered projection: every original
# Some occurrence, including duplicate keys/payloads, is present at its exact
# prefix-Some rank. This complements exact full-list/operation concatenation.
import Base
import ./QueryFilterMapModel.bend as M
import ../contract/Data.bend as D
import ../proof/Foundations.bend as F
import ./SequencePaginationProofs.bend as Position

def key_at(keys: List<&2,String>,position: Nat) -> Maybe<&2,String>:
  match keys position:
    case Nil{} position: None{}
    case Con{head,tail} 0n: Some{head}
    case Con{head,tail} 1n+previous: key_at(tail,previous)

def start(~Env: Data,~cost: Env -> String -> Nat -> Nat,+env: Env,keys: List<&2,String>,position: Nat,+index: Nat) -> Nat:
  match keys position:
    case Nil{} position: index
    case Con{head,tail} 0n: index
    case Con{+head,tail} 1n+previous: start(~Env,~cost,env,tail,previous,Nat.add(cost(env,head,index),index))

def advance(item: Maybe<&2,D.Value>,rank: Nat) -> Nat:
  match item:
    case None{}: rank
    case Some{value}: 1n+rank

def before(~Env: Data,~cost: Env -> String -> Nat -> Nat,~item: Env -> String -> Nat -> Maybe<&2,D.Value>,+env: Env,keys: List<&2,String>,position: Nat,+index: Nat) -> Nat:
  match keys position:
    case Nil{} position: 0n
    case Con{head,tail} 0n: 0n
    case Con{+head,tail} 1n+previous: advance(item(env,head,index),before(~Env,~cost,~item,env,tail,previous,Nat.add(cost(env,head,index),index)))

law preceding_projection_changes_tail_ranks_only_by_its_own_presence:
  for +item: Maybe<&2,D.Value>
  for +tail: List<&2,D.Value>
  for +rank: Nat
  for +value: D.Value
  for found: {Position.at(tail,rank) == Some{value} : Maybe<&2,D.Value>}
  {Position.at(M.push(item,tail),advance(item,rank)) == Some{value} : Maybe<&2,D.Value>}
def preceding_projection_changes_tail_ranks_only_by_its_own_presence(item,tail,rank,value,found):
  match item:
    case None{}: found
    case Some{head}: found

law present_head_projection_has_the_exact_payload_at_output_zero:
  for +item: Maybe<&2,D.Value>
  for +tail: List<&2,D.Value>
  for +value: D.Value
  for exact: {item == Some{value} : Maybe<&2,D.Value>}
  {Position.at(M.push(item,tail),0n) == Some{value} : Maybe<&2,D.Value>}
def present_head_projection_has_the_exact_payload_at_output_zero(item,tail,value,exact):
  Equal.cong(Maybe<&2,D.Value>,Maybe<&2,D.Value>,head => Position.at(M.push(head,tail),0n),item,Some{value},exact)

law every_original_projected_occurrence_is_retained_at_its_exact_prefix_rank:
  for ~Env: Data
  for ~cost: Env -> String -> Nat -> Nat
  for ~item: Env -> String -> Nat -> Maybe<&2,D.Value>
  for +env: Env
  for +keys: List<&2,String>
  for +position: Nat
  for +index: Nat
  for +key: String
  for +value: D.Value
  for present: {key_at(keys,position) == Some{key} : Maybe<&2,String>}
  for projected: {item(env,key,start(~Env,~cost,env,keys,position,index)) == Some{value} : Maybe<&2,D.Value>}
  {Position.at(M.items(~Env,~cost,~item,env,keys,index),before(~Env,~cost,~item,env,keys,position,index)) == Some{value} : Maybe<&2,D.Value>}
def every_original_projected_occurrence_is_retained_at_its_exact_prefix_rank(Env,cost,item,env,keys,position,index,key,value,present,projected):
  match keys position:
    case Nil{} position: Empty.absurd({Position.at(M.items(~Env,~cost,~item,env,Nil{},index),before(~Env,~cost,~item,env,Nil{},position,index)) == Some{value} : Maybe<&2,D.Value>},F.none_negative_some(String,key,present))
    case Con{+head,+tail} 0n:
      present_head_projection_has_the_exact_payload_at_output_zero(item(env,head,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,head,index),index)),value,Equal.trans(Maybe<&2,D.Value>,item(env,head,index),item(env,key,index),Some{value},Equal.cong(String,Maybe<&2,D.Value>,k => item(env,k,index),head,key,F.some_injective(String,head,key,present)),projected))
    case Con{+head,+tail} 1n+previous:
      preceding_projection_changes_tail_ranks_only_by_its_own_presence(item(env,head,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,head,index),index)),before(~Env,~cost,~item,env,tail,previous,Nat.add(cost(env,head,index),index)),value,every_original_projected_occurrence_is_retained_at_its_exact_prefix_rank(~Env,~cost,~item,env,tail,previous,Nat.add(cost(env,head,index),index),key,value,present,projected))
