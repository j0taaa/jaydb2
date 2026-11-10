# Real renderer queries establish their own local bounds. No global-order,
# Current, chosen-observer or final-state conclusion is a primitive premise.
import Base
import ../../../contract/Logic.bend as L
import ../../Foundations.bend as F
import ../../ProtocolService.bend as Q
import ./TimeEmbedding.bend as T

def count(-A: Data, items: List<&2, A>) -> Nat:
  match items:
    case Nil{}: 0n
    case Con{head, rest}: 1n+count(A, rest)

def query(-A: Data, items: List<&2, A>, index: Nat) -> Maybe<&2, A>:
  match items index:
    case Nil{} _: None{}
    case Con{head, rest} 0n: Some{head}
    case Con{head, rest} 1n+k: query(A, rest, k)

law successful_query_is_strictly_inside_actual_list:
  for -A: Data
  for items: List<&2, A>
  for index: Nat
  for -item: A
  for found: {query(A, items, index) == Some{item} : Maybe<&2, A>}
  {Nat.is_lt(index, count(A, items)) == True{} : Bool}
def successful_query_is_strictly_inside_actual_list(A, items, index, item, found):
  match items index:
    case Nil{} _: L.ex_false({Nat.is_lt(index, 0n) == True{} : Bool}, F.none_negative_some(A, item, found))
    case Con{head, rest} 0n: {==}
    case Con{head, rest} 1n+k: successful_query_is_strictly_inside_actual_list(A, rest, k, item, found)

def lengths(-A: Data, blocks: List<&2, List<&2, A>>) -> List<&2, Nat>:
  match blocks:
    case Nil{}: Nil{}
    case Con{head, rest}: Con{count(A, head), lengths(A, rest)}

law real_nested_queries_establish_the_phase_local_bound:
  for -A: Data
  for blocks: List<&2, List<&2, A>>
  for owner: Nat
  for +items: List<&2, A>
  for +local: Nat
  for -item: A
  for block_found: {query(List<&2, A>, blocks, owner) == Some{items} : Maybe<&2, List<&2, A>>}
  for event_found: {query(A, items, local) == Some{item} : Maybe<&2, A>}
  T.Local(lengths(A, blocks), owner, local)
def real_nested_queries_establish_the_phase_local_bound(A, blocks, owner, items, local, item, block_found, event_found):
  match blocks owner:
    case Nil{} _: L.ex_false(Empty, F.none_negative_some(List<&2, A>, items, block_found))
    case Con{+head, rest} 0n:
      %Equal.sym(List<&2, A>, head, items, F.some_injective(List<&2, A>, head, items, block_found)) :
        {Nat.is_lt(local, count(A, _)) == True{} : Bool}
      successful_query_is_strictly_inside_actual_list(A, items, local, item, event_found)
    case Con{head, rest} 1n+k:
      real_nested_queries_establish_the_phase_local_bound(A, rest, k, items, local, item, block_found, event_found)

law generic_query_is_exact_existing_protocol_query:
  for items: List<&2, Q.Frame>
  for index: Nat
  {query(Q.Frame, items, index) == Q.query(items, index) : Maybe<&2, Q.Frame>}
def generic_query_is_exact_existing_protocol_query(items, index):
  match items index:
    case Nil{} _: {==}
    case Con{head, rest} 0n: {==}
    case Con{head, rest} 1n+k: generic_query_is_exact_existing_protocol_query(rest, k)

law generic_count_is_exact_existing_protocol_size:
  for items: List<&2, Q.Frame>
  {count(Q.Frame, items) == Q.size(items) : Nat}
def generic_count_is_exact_existing_protocol_size(items):
  match items:
    case Nil{}: {==}
    case Con{head, +rest}:
      Equal.cong(Nat, Nat, n => Succ{n}, count(Q.Frame, rest), Q.size(rest), generic_count_is_exact_existing_protocol_size(rest))

law actual_protocol_query_supplies_its_own_block_bound:
  for +items: List<&2, Q.Frame>
  for +index: Nat
  for -item: Q.Frame
  for found: {Q.query(items, index) == Some{item} : Maybe<&2, Q.Frame>}
  {Nat.is_lt(index, Q.size(items)) == True{} : Bool}
def actual_protocol_query_supplies_its_own_block_bound(items, index, item, found):
  %generic_count_is_exact_existing_protocol_size(items) : {Nat.is_lt(index, _) == True{} : Bool}
  successful_query_is_strictly_inside_actual_list(Q.Frame, items, index, item,
    Equal.trans(Maybe<&2, Q.Frame>, query(Q.Frame, items, index), Q.query(items, index), Some{item},
      generic_query_is_exact_existing_protocol_query(items, index), found))
