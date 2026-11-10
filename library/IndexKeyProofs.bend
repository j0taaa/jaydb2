# All-character structural key laws. Unique keys identify parts; nonunique
# keys identify the full (parts,target) pair. Mixed modes require a namespace
# or fixed-arity domain: differing arities can deliberately share a string.
import Base
import ../contract/Data.bend as D
import ./Index.bend as Index
import ./Key.bend as Key
import ./ValueScalarProofs.bend as Pair
import ../proof/Foundations.bend as F

def first(xs: List<&2,String>) -> String:
  match xs:
    case Nil{}: ""
    case Con{head,tail}: head

def length(xs: List<&2,String>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{head,tail}: 1n+length(tail)

law appending_one_target_is_nonempty_for_every_parts_list:
  for +parts: List<&2,String>
  for +target: String
  {List.is_empty(&2,String,Index.append(parts,[target])) == False{} : Bool}
def appending_one_target_is_nonempty_for_every_parts_list(parts,target):
  match parts:
    case Nil{}: {==}
    case Con{head,tail}: {==}

def empty_cannot_be_appended_target(+parts: List<&2,String>,+target: String,same: {Nil{} == Index.append(parts,[target]) : List<&2,String>}) -> Empty:
  F.false_negative_true(Equal.trans(Bool,False{},List.is_empty(&2,String,Index.append(parts,[target])),True{},Equal.sym(Bool,List.is_empty(&2,String,Index.append(parts,[target])),False{},appending_one_target_is_nonempty_for_every_parts_list(parts,target)),Equal.cong(List<&2,String>,Bool,items => List.is_empty(&2,String,items),Index.append(parts,[target]),Nil{},Equal.sym(List<&2,String>,Nil{},Index.append(parts,[target]),same))))

def lift_appended_prefix(+head: String,+tail: List<&2,String>,+other_head: String,+other_tail: List<&2,String>,+target: String,+other_target: String,heads: {head == other_head : String},pair: Pair.Both<{tail == other_tail : List<&2,String>},{target == other_target : String}>) -> Pair.Both<{Con{head,tail} == Con{other_head,other_tail} : List<&2,String>},{target == other_target : String}>:
  match pair:
    case Pair.Both{prefix,last}: Pair.Both{Equal.trans(List<&2,String>,Con{head,tail},Con{other_head,tail},Con{other_head,other_tail},Equal.cong(String,List<&2,String>,h => Con{h,tail},head,other_head,heads),Equal.cong(List<&2,String>,List<&2,String>,t => Con{other_head,t},tail,other_tail,prefix)),last}

law appending_a_single_target_is_injective_in_both_parts_and_target:
  for +parts: List<&2,String>
  for +other: List<&2,String>
  for +target: String
  for +other_target: String
  for +same: {Index.append(parts,[target]) == Index.append(other,[other_target]) : List<&2,String>}
  Pair.Both<{parts == other : List<&2,String>},{target == other_target : String}>
def appending_a_single_target_is_injective_in_both_parts_and_target(parts,other,target,other_target,same):
  match parts other:
    case Nil{} Nil{}: Pair.Both{{==},Equal.cong(List<&2,String>,String,first,[target],[other_target],same)}
    case Nil{} Con{head,+tail}: Empty.absurd(Pair.Both<{Nil{} == Con{head,tail} : List<&2,String>},{target == other_target : String}>,empty_cannot_be_appended_target(tail,other_target,Equal.cong(List<&2,String>,List<&2,String>,items => List.tail(&2,String,items),[target],Index.append(Con{head,tail},[other_target]),same)))
    case Con{head,+tail} Nil{}: Empty.absurd(Pair.Both<{Con{head,tail} == Nil{} : List<&2,String>},{target == other_target : String}>,empty_cannot_be_appended_target(tail,target,Equal.sym(List<&2,String>,Index.append(tail,[target]),Nil{},Equal.cong(List<&2,String>,List<&2,String>,items => List.tail(&2,String,items),Index.append(Con{head,tail},[target]),[other_target],same))))
    case Con{+head,+tail} Con{+other_head,+other_tail}:
      +heads = Equal.cong(List<&2,String>,String,first,Index.append(Con{head,tail},[target]),Index.append(Con{other_head,other_tail},[other_target]),same)
      lift_appended_prefix(head,tail,other_head,other_tail,target,other_target,heads,appending_a_single_target_is_injective_in_both_parts_and_target(tail,other_tail,target,other_target,Equal.cong(List<&2,String>,List<&2,String>,items => List.tail(&2,String,items),Index.append(Con{head,tail},[target]),Index.append(Con{other_head,other_tail},[other_target]),same)))

law unique_row_keys_are_injective_in_the_complete_parts_list:
  for +parts: List<&2,String>
  for +other: List<&2,String>
  for -target: String
  for -other_target: String
  for same: {D.row_key(Index.unique(parts,target)) == D.row_key(Index.unique(other,other_target)) : String}
  {parts == other : List<&2,String>}
def unique_row_keys_are_injective_in_the_complete_parts_list(parts,other,target,other_target,same): Key.injective(parts,other,same)

law nonunique_row_keys_are_injective_in_parts_and_target_without_an_arity_assumption:
  for +parts: List<&2,String>
  for +other: List<&2,String>
  for +target: String
  for +other_target: String
  for same: {D.row_key(Index.nonunique(parts,target)) == D.row_key(Index.nonunique(other,other_target)) : String}
  Pair.Both<{parts == other : List<&2,String>},{target == other_target : String}>
def nonunique_row_keys_are_injective_in_parts_and_target_without_an_arity_assumption(parts,other,target,other_target,same):
  appending_a_single_target_is_injective_in_both_parts_and_target(parts,other,target,other_target,Key.injective(Index.append(parts,[target]),Index.append(other,[other_target]),same))

law appended_target_adds_exactly_one_part:
  for +parts: List<&2,String>
  for +target: String
  {length(Index.append(parts,[target])) == 1n+length(parts) : Nat}
def appended_target_adds_exactly_one_part(parts,target):
  match parts:
    case Nil{}: {==}
    case Con{head,+tail}: Equal.cong(Nat,Nat,n => 1n+n,length(Index.append(tail,[target])),1n+length(tail),appended_target_adds_exactly_one_part(tail,target))

def predecessor(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+previous: previous

def zero(n: Nat) -> Bool:
  match n:
    case 0n: True{}
    case 1n+previous: False{}

def a_natural_cannot_equal_its_successor(+n: Nat,same: {n == 1n+n : Nat}) -> Empty:
  match n:
    case 0n: F.false_negative_true(Equal.cong(Nat,Bool,zero,1n,0n,Equal.sym(Nat,0n,1n,same)))
    case 1n+previous: a_natural_cannot_equal_its_successor(previous,Equal.cong(Nat,Nat,predecessor,1n+previous,2n+previous,same))

law unique_and_nonunique_keys_of_equal_parts_arity_never_collide:
  for +parts: List<&2,String>
  for +other: List<&2,String>
  for +target: String
  for +other_target: String
  for arity: {length(parts) == length(other) : Nat}
  for same: {D.row_key(Index.unique(parts,target)) == D.row_key(Index.nonunique(other,other_target)) : String}
  Empty
def unique_and_nonunique_keys_of_equal_parts_arity_never_collide(parts,other,target,other_target,arity,same):
  a_natural_cannot_equal_its_successor(length(other),Equal.trans(Nat,length(other),length(parts),1n+length(other),Equal.sym(Nat,length(parts),length(other),arity),Equal.trans(Nat,length(parts),length(Index.append(other,[other_target])),1n+length(other),Equal.cong(List<&2,String>,Nat,length,parts,Index.append(other,[other_target]),Key.injective(parts,Index.append(other,[other_target]),same)),appended_target_adds_exactly_one_part(other,other_target))))

# A checked general collision outside that domain; no format/law is changed.
law mixed_arities_can_share_a_unique_and_nonunique_key:
  for +parts: List<&2,String>
  for +target: String
  for -unique_target: String
  {D.row_key(Index.unique(Index.append(parts,[target]),unique_target)) == D.row_key(Index.nonunique(parts,target)) : String}
def mixed_arities_can_share_a_unique_and_nonunique_key(parts,target,unique_target): {==}
