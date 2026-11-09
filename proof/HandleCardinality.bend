# Constructive finite cardinality and actual bounded membership search.
import Base
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./Orders.bend as O

def length(xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{x, rest}: 1n+length(rest)

def Has(-key: String, keys: List<&2, String>) -> Type:
  match keys:
    case Nil{}: Empty
    case Con{head, rest}: L.Disjunction<{key == head : String}, Has(key, rest)>

def Absent(-key: String, keys: List<&2, String>) -> Type:
  match keys:
    case Nil{}: Unit
    case Con{head, rest}: L.E<({key == head : String} -> Empty), Absent(key, rest)>

def Unique(keys: List<&2, String>) -> Type:
  match keys:
    case Nil{}: Unit
    case Con{head, rest}: L.E<Absent(head, rest), Unique(rest)>

def Subset(candidates: List<&2, String>, -keys: List<&2, String>) -> Type:
  match candidates:
    case Nil{}: Unit
    case Con{head, rest}: L.E<Has(head, keys), Subset(rest, keys)>

# Membership at a real list index contains only data equalities. It can be
# reused constructively; arbitrary affine proof functions are never copied.
def At(index: Nat, -key: String, keys: List<&2, String>) -> Data:
  match index keys:
    case _ Nil{}: Empty
    case 0n Con{head, rest}: {key == head : String}
    case 1n+k Con{head, rest}: At(k, key, rest)

def remove_at(index: Nat, keys: List<&2, String>) -> List<&2, String>:
  match index keys:
    case _ Nil{}: Nil{}
    case 0n Con{head, rest}: rest
    case 1n+k Con{head, rest}: Con{head, remove_at(k, rest)}

def Le(n: Nat, m: Nat) -> Data:
  match n m:
    case 0n _: Unit
    case 1n+n 0n: Empty
    case 1n+n 1n+m: Le(n, m)

law successor_cannot_be_bounded_by_itself:
  for n: Nat
  for impossible: Le(1n+n, n)
  Empty
def successor_cannot_be_bounded_by_itself(n, impossible):
  match n:
    case 0n: impossible
    case 1n+k: successor_cannot_be_bounded_by_itself(k, impossible)

def lift_position(-key: String, -head: String, -tail: List<&2, String>,
  found: &index: Nat -> L.E<At(index, key, tail), Unit>) ->
  &index: Nat -> L.E<At(index, key, Con{head, tail}), Unit>:
  (index, L.Both{witness, unit}) = found
  (1n+index, L.Both{witness, unit})

law present_key_has_actual_position:
  for +keys: List<&2, String>
  for +key: String
  for present: Has(key, keys)
  exs index: Nat
  L.E<At(index, key, keys), Unit>
def present_key_has_actual_position(keys, key, present):
  match keys present:
    case Nil{} impossible: match impossible:
    case Con{head, rest} L.Left{same}: (0n, L.Both{same, Unit{}})
    case Con{head, rest} L.Right{later}:
      lift_position(key, head, rest, present_key_has_actual_position(rest, key, later))

law actual_removal_decreases_cardinality:
  for +index: Nat
  for +keys: List<&2, String>
  for -key: String
  for actual: At(index, key, keys)
  {length(keys) == 1n+length(remove_at(index, keys)) : Nat}
def actual_removal_decreases_cardinality(index, keys, key, actual):
  match index keys:
    case _ Nil{}: match actual:
    case 0n Con{head, rest}: {==}
    case 1n+k Con{head, +rest}:
      Equal.cong(Nat, Nat, n => 1n+n, length(rest), 1n+length(remove_at(k, rest)),
        actual_removal_decreases_cardinality(k, rest, key, actual))

law other_key_survives_removal:
  for +index: Nat
  for +keys: List<&2, String>
  for +key: String
  for +other: String
  for actual: At(index, key, keys)
  for different: {other == key : String} -> Empty
  for present: Has(other, keys)
  Has(other, remove_at(index, keys))
def other_key_survives_removal(index, keys, key, other, actual, different, present):
  match index keys present:
    case _ Nil{} impossible: match impossible:
    case 0n Con{+head, rest} L.Left{same}:
      L.ex_false(Has(other, rest), different(Equal.trans(String, other, head, key,
        same, Equal.sym(String, key, head, actual))))
    case 0n Con{head, rest} L.Right{later}: later
    case 1n+k Con{head, rest} L.Left{same}: L.Left{same}
    case 1n+k Con{head, rest} L.Right{later}:
      L.Right{other_key_survives_removal(k, rest, key, other, actual, different, later)}

def subset_after_removal(+candidates: List<&2, String>, +key: String,
  +keys: List<&2, String>, +index: Nat, +actual: At(index, key, keys),
  absent: Absent(key, candidates), subset: Subset(candidates, keys)) ->
  Subset(candidates, remove_at(index, keys)):
  match candidates absent subset:
    case Nil{} _ _: Unit{}
    case Con{+head, +tail} L.Both{different, later_absent} L.Both{present, later_subset}:
      L.Both{other_key_survives_removal(index, keys, key, head, actual,
          equal => different(Equal.sym(String, head, key, equal)), present),
        subset_after_removal(tail, key, keys, index, actual, later_absent, later_subset)}

def bound_after_position(+head: String, +tail: List<&2, String>, +keys: List<&2, String>,
  absent: Absent(head, tail), subset: Subset(tail, keys),
  position: &index: Nat -> L.E<At(index, head, keys), Unit>,
  recurse: @remaining: List<&2, String> -> Subset(tail, remaining) -> Le(length(tail), length(remaining))) ->
  Le(1n+length(tail), length(keys)):
  (+index, L.Both{+actual, unit}) = position
  %Equal.sym(Nat, length(keys), 1n+length(remove_at(index, keys)),
    actual_removal_decreases_cardinality(index, keys, head, actual)) : Le(1n+length(tail), _)
  recurse(remove_at(index, keys), subset_after_removal(tail, head, keys, index, actual, absent, subset))

law unique_subset_cannot_exceed_registry_cardinality:
  for +candidates: List<&2, String>
  for +keys: List<&2, String>
  for unique: Unique(candidates)
  for subset: Subset(candidates, keys)
  Le(length(candidates), length(keys))
def unique_subset_cannot_exceed_registry_cardinality(candidates, keys, unique, subset):
  match candidates unique subset:
    case Nil{} _ _: Unit{}
    case Con{+head, +tail} L.Both{absent, unique_tail} L.Both{present, subset_tail}:
      bound_after_position(head, tail, keys, absent, subset_tail,
        present_key_has_actual_position(keys, head, present),
        remaining => retained => unique_subset_cannot_exceed_registry_cardinality(tail,
          remaining, unique_tail, retained))

def member(+needle: String, keys: List<&2, String>) -> Bool:
  match keys:
    case Nil{}: False{}
    case Con{head, rest}: String.eq(needle, head) || member(needle, rest)

def member_case(same: Bool, +needle: String, +head: String, -tail: List<&2, String>,
  checked: {String.eq(needle, head) == same : Bool},
  accepted: {same || member(needle, tail) == True{} : Bool},
  later: {member(needle, tail) == True{} : Bool} -> Has(needle, tail)) -> Has(needle, Con{head, tail}):
  match same:
    case False{}: L.Right{later(accepted)}
    case True{}: L.Left{O.string_equal(needle, head, checked)}

law actual_membership_establishes_presence:
  for +keys: List<&2, String>
  for +needle: String
  for accepted: {member(needle, keys) == True{} : Bool}
  Has(needle, keys)
def actual_membership_establishes_presence(keys, needle, accepted):
  match keys:
    case Nil{}: F.absurd_boolean(Has(needle, Nil{}), accepted)
    case Con{+head, +tail}:
      member_case(String.eq(needle, head), needle, head, tail, {==}, accepted,
        found => actual_membership_establishes_presence(tail, needle, found))

def search_member(found: Bool, candidate: String, later: Maybe<&2, String>) -> Maybe<&2, String>:
  match found:
    case False{}: Some{candidate}
    case True{}: later

def search(candidates: List<&2, String>, +keys: List<&2, String>) -> Maybe<&2, String>:
  match candidates:
    case Nil{}: None{}
    case Con{+head, tail}: search_member(member(head, keys), head, search(tail, keys))

def ValidSearch(result: Maybe<&2, String>, candidates: List<&2, String>,
  keys: List<&2, String>) -> Type:
  match result:
    case None{}: Subset(candidates, keys)
    case Some{key}: {member(key, keys) == False{} : Bool}

def found_search_result(result: Maybe<&2, String>, -head: String,
  -tail: List<&2, String>, -keys: List<&2, String>, present: Has(head, keys),
  valid: ValidSearch(result, tail, keys)) -> ValidSearch(result, Con{head, tail}, keys):
  match result:
    case None{}: L.Both{present, valid}
    case Some{key}: valid

def search_branch(found: Bool, +head: String, -tail: List<&2, String>,
  +keys: List<&2, String>, +result: Maybe<&2, String>,
  checked: {member(head, keys) == found : Bool}, valid: ValidSearch(result, tail, keys)) ->
  ValidSearch(search_member(found, head, result), Con{head, tail}, keys):
  match found:
    case False{}: checked
    case True{}:
      found_search_result(result, head, tail, keys,
        actual_membership_establishes_presence(keys, head, checked), valid)

law bounded_search_has_checked_result:
  for +candidates: List<&2, String>
  for +keys: List<&2, String>
  ValidSearch(search(candidates, keys), candidates, keys)
def bounded_search_has_checked_result(candidates, keys):
  match candidates:
    case Nil{}: Unit{}
    case Con{+head, +tail}:
      search_branch(member(head, keys), head, tail, keys, search(tail, keys), {==},
        bounded_search_has_checked_result(tail, keys))

def complete_search_result(result: Maybe<&2, String>, +candidates: List<&2, String>,
  +keys: List<&2, String>, unique: Unique(candidates),
  count: {length(candidates) == 1n+length(keys) : Nat},
  exact: {search(candidates, keys) == result : Maybe<&2, String>},
  valid: ValidSearch(result, candidates, keys)) ->
  &found: String -> L.E<{search(candidates, keys) == Some{found} : Maybe<&2, String>},
    {member(found, keys) == False{} : Bool}>:
  match result:
    case None{}:
      L.ex_false((&found: String -> L.E<{search(candidates, keys) == Some{found} : Maybe<&2, String>},
        {member(found, keys) == False{} : Bool}>),
        successor_cannot_be_bounded_by_itself(length(keys),
          (%count : Le(_, length(keys))
            unique_subset_cannot_exceed_registry_cardinality(candidates, keys, unique, valid))))
    case Some{found}: (found, L.Both{exact, valid})

law finite_fresh_search_from_real_cardinality:
  for +candidates: List<&2, String>
  for +keys: List<&2, String>
  for unique: Unique(candidates)
  for count: {length(candidates) == 1n+length(keys) : Nat}
  exs found: String
  L.E<{search(candidates, keys) == Some{found} : Maybe<&2, String>},
    {member(found, keys) == False{} : Bool}>
def finite_fresh_search_from_real_cardinality(candidates, keys, unique, count):
  complete_search_result(search(candidates, keys), candidates, keys, unique, count,
    {==}, bounded_search_has_checked_result(candidates, keys))

law le_reflexive:
  for n: Nat
  Le(n, n)
def le_reflexive(n):
  match n:
    case 0n: Unit{}
    case 1n+k: le_reflexive(k)

law le_transitive:
  for n: Nat
  for m: Nat
  for k: Nat
  for nm: Le(n, m)
  for mk: Le(m, k)
  Le(n, k)
def le_transitive(n, m, k, nm, mk):
  match n m k:
    case 0n _ _: Unit{}
    case 1n+n 0n _: match nm:
    case 1n+n 1n+m 0n: match mk:
    case 1n+n 1n+m 1n+k: le_transitive(n, m, k, nm, mk)

law le_weaken_successor:
  for n: Nat
  for m: Nat
  for next: Le(1n+n, m)
  Le(n, m)
def le_weaken_successor(n, m, next):
  match n m:
    case 0n _: Unit{}
    case 1n+k 0n: match next:
    case 1n+k 1n+m: le_weaken_successor(k, m, next)

law le_as_actual_boolean:
  for n: Nat
  for m: Nat
  for bounded: Le(n, m)
  {Nat.is_le(n, m) == True{} : Bool}
def le_as_actual_boolean(n, m, bounded):
  match n m:
    case 0n 0n: {==}
    case 0n 1n+k: {==}
    case 1n+k 0n: match bounded:
    case 1n+k 1n+m: le_as_actual_boolean(k, m, bounded)

law actual_boolean_as_le:
  for n: Nat
  for m: Nat
  for bounded: {Nat.is_le(n, m) == True{} : Bool}
  Le(n, m)
def actual_boolean_as_le(n, m, bounded):
  match n m:
    case 0n _: Unit{}
    case 1n+k 0n: F.absurd_boolean(Le(1n+k, 0n), bounded)
    case 1n+k 1n+m: actual_boolean_as_le(k, m, bounded)

def candidate_branch(found: Bool, +head: String, -tail: List<&2, String>,
  -keys: List<&2, String>, +value: String,
  exact: {search_member(found, head, search(tail, keys)) == Some{value} : Maybe<&2, String>},
  later: {search(tail, keys) == Some{value} : Maybe<&2, String>} -> Has(value, tail)) ->
  Has(value, Con{head, tail}):
  match found:
    case False{}:
      L.Left{Equal.sym(String, head, value, F.some_injective(String, head, value, exact))}
    case True{}: L.Right{later(exact)}

law returned_search_value_is_an_actual_candidate:
  for +candidates: List<&2, String>
  for +keys: List<&2, String>
  for +value: String
  for exact: {search(candidates, keys) == Some{value} : Maybe<&2, String>}
  Has(value, candidates)
def returned_search_value_is_an_actual_candidate(candidates, keys, value, exact):
  match candidates:
    case Nil{}:
      L.ex_false(Has(value, Nil{}), F.none_negative_some(String, value, exact))
    case Con{+head, +tail}:
      candidate_branch(member(head, keys), head, tail, keys, value, exact,
        returned => returned_search_value_is_an_actual_candidate(tail, keys, value, returned))

# Independent literal absence, stronger than a Boolean label. This uses actual
# comparator reflexivity, so an always-false membership mutation cannot pass.
def equal_implies_string_test(+key: String, +head: String,
  same: {key == head : String}) -> {String.eq(key, head) == True{} : Bool}:
  %Equal.sym(String, key, head, same) : {String.eq(_, head) == True{} : Bool}
  O.string_eq_refl(head)

def absent_branch(found: Bool, +key: String, +head: String, -tail: List<&2, String>,
  checked: {String.eq(key, head) == found : Bool},
  absent: {found || member(key, tail) == False{} : Bool},
  later: {member(key, tail) == False{} : Bool} -> Absent(key, tail)) ->
  Absent(key, Con{head, tail}):
  match found:
    case False{}:
      L.Both{same => F.false_negative_true(Equal.trans(Bool, False{}, String.eq(key, head), True{},
        Equal.sym(Bool, String.eq(key, head), False{}, checked),
        equal_implies_string_test(key, head, same))), later(absent)}
    case True{}:
      L.ex_false(Absent(key, Con{head, tail}),
        F.false_negative_true(Equal.sym(Bool, True{}, False{}, absent)))

law actual_failed_membership_establishes_literal_absence:
  for +keys: List<&2, String>
  for +key: String
  for absent: {member(key, keys) == False{} : Bool}
  Absent(key, keys)
def actual_failed_membership_establishes_literal_absence(keys, key, absent):
  match keys:
    case Nil{}: Unit{}
    case Con{+head, +tail}:
      absent_branch(String.eq(key, head), key, head, tail, {==}, absent,
        missing => actual_failed_membership_establishes_literal_absence(tail, key, missing))
