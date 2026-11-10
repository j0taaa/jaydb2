# Arithmetic order of the independent occurrence ranks. These lemmas use only
# original positions and mathematical row weights, never a claimed join order.
import Base
import ./RelationRows.bend as Rows
import ./RelationModel.bend as M
import ./SequencePaginationProofs.bend as Position
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Int64Proofs.bend as Arithmetic
import ../proof/Foundations.bend as F

law common_prefix_preserves_strict_natural_comparison:
  for +prefix: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(Nat.add(prefix,a),Nat.add(prefix,b)) == Nat.is_lt(a,b) : Bool}
def common_prefix_preserves_strict_natural_comparison(prefix,a,b):
  match prefix:
    case 0n: {==}
    case 1n+previous: common_prefix_preserves_strict_natural_comparison(previous,a,b)

law strict_bound_remains_strict_after_appending_any_tail:
  for +a: Nat
  for +bound: Nat
  for +tail: Nat
  for strict: {Nat.is_lt(a,bound) == True{} : Bool}
  {Nat.is_lt(a,Nat.add(bound,tail)) == True{} : Bool}
def strict_bound_remains_strict_after_appending_any_tail(a,bound,tail,strict):
  match a bound:
    case 0n 0n: F.absurd_boolean({Nat.is_lt(0n,tail) == True{} : Bool},strict)
    case 0n 1n+previous: {==}
    case 1n+previous 0n: F.absurd_boolean({Nat.is_lt(1n+previous,tail) == True{} : Bool},strict)
    case 1n+previous 1n+smaller: strict_bound_remains_strict_after_appending_any_tail(previous,smaller,tail,strict)

law an_inside_row_rank_strictly_precedes_every_later_left_source_prefix:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +first: Nat
  for +later: Nat
  for +value: D.Value
  for +relative: Nat
  for present: {Position.at(left,first) == Some{value} : Maybe<&2,D.Value>}
  for inside: {Nat.is_lt(relative,M.row_count(~left_key,~right_key,outer,value,right)) == True{} : Bool}
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,left,right,first),relative),M.before_left(~left_key,~right_key,outer,left,right,later)) == True{} : Bool}
def an_inside_row_rank_strictly_precedes_every_later_left_source_prefix(left_key,right_key,outer,left,right,first,later,value,relative,present,inside,ordered):
  match left:
    case Nil{}: L.ex_false({Nat.is_lt(relative,0n) == True{} : Bool},F.none_negative_some(D.Value,value,present))
    case Con{+head,+tail}:
      match first later:
        case 0n 0n: F.absurd_boolean({Nat.is_lt(relative,0n) == True{} : Bool},ordered)
        case 0n 1n+after:
          strict_bound_remains_strict_after_appending_any_tail(relative,M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,after),
            Equal.trans(Bool,Nat.is_lt(relative,M.row_count(~left_key,~right_key,outer,head,right)),Nat.is_lt(relative,M.row_count(~left_key,~right_key,outer,value,right)),True{},Equal.cong(D.Value,Bool,item => Nat.is_lt(relative,M.row_count(~left_key,~right_key,outer,item,right)),head,value,Selection.equal_present_values_have_equal_payloads(head,value,present)),inside))
        case 1n+previous 0n: F.absurd_boolean({Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,Con{head,tail},right,1n+previous),relative),0n) == True{} : Bool},ordered)
        case 1n+previous 1n+after:
          Equal.trans(Bool,Nat.is_lt(Nat.add(Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,previous)),relative),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,after))),Nat.is_lt(Nat.add(M.row_count(~left_key,~right_key,outer,head,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative)),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,after))),True{},
            Equal.cong(Nat,Bool,n => Nat.is_lt(n,Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,after))),Nat.add(Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,previous)),relative),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative)),Arithmetic.add_associative(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,previous),relative)),
            Equal.trans(Bool,Nat.is_lt(Nat.add(M.row_count(~left_key,~right_key,outer,head,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative)),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,after))),Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative),M.before_left(~left_key,~right_key,outer,tail,right,after)),True{},common_prefix_preserves_strict_natural_comparison(M.row_count(~left_key,~right_key,outer,head,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative),M.before_left(~left_key,~right_key,outer,tail,right,after)),an_inside_row_rank_strictly_precedes_every_later_left_source_prefix(~left_key,~right_key,outer,tail,right,previous,after,value,relative,present,inside,ordered)))

# The actual origin theorem proves the "inside" condition for every emitted
# row occurrence, so this yields strict left-major order for actual outputs.
law every_earlier_left_row_occurrence_strictly_precedes_every_later_left_row_rank:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +first: Nat
  for +later: Nat
  for +value: D.Value
  for +relative: Nat
  for +later_relative: Nat
  for present: {Position.at(left,first) == Some{value} : Maybe<&2,D.Value>}
  for inside: {Nat.is_lt(relative,M.row_count(~left_key,~right_key,outer,value,right)) == True{} : Bool}
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,left,right,first),relative),Nat.add(M.before_left(~left_key,~right_key,outer,left,right,later),later_relative)) == True{} : Bool}
def every_earlier_left_row_occurrence_strictly_precedes_every_later_left_row_rank(left_key,right_key,outer,left,right,first,later,value,relative,later_relative,present,inside,ordered):
  strict_bound_remains_strict_after_appending_any_tail(Nat.add(M.before_left(~left_key,~right_key,outer,left,right,first),relative),M.before_left(~left_key,~right_key,outer,left,right,later),later_relative,an_inside_row_rank_strictly_precedes_every_later_left_source_prefix(~left_key,~right_key,outer,left,right,first,later,value,relative,present,inside,ordered))

law matching_right_occurrences_keep_their_strict_order_inside_the_same_left_prefix:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +left_index: Nat
  for +left_value: D.Value
  for +first: Nat
  for +later: Nat
  for +right_value: D.Value
  for present: {Position.at(right,first) == Some{right_value} : Maybe<&2,D.Value>}
  for matched: {String.eq(left_key(left_value),right_key(right_value)) == True{} : Bool}
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,first)),Nat.add(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,later))) == True{} : Bool}
def matching_right_occurrences_keep_their_strict_order_inside_the_same_left_prefix(left_key,right_key,outer,left,right,left_index,left_value,first,later,right_value,present,matched,ordered):
  Equal.trans(Bool,Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,first)),Nat.add(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,later))),Nat.is_lt(Selection.before(~Rows.selected(~right_key),left_key(left_value),right,first),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,later)),True{},common_prefix_preserves_strict_natural_comparison(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,first),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,later)),Rows.matching_right_source_positions_preserve_strict_output_order(~left_key,~right_key,left_value,right,first,later,right_value,present,matched,ordered))
