# Descending len..0 counter search: cardinality proof before specialization to
# the independently proved concrete lowercase hexadecimal encoder.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ./HandleCardinality.bend as F
import ./HandleHex.bend as H

def candidates(~key: Nat -> String, +n: Nat) -> List<&2, String>:
  match n:
    case 0n: [key(0n)]
    case 1n+k: Con{key(1n+k), candidates(key, k)}

law candidate_count:
  for ~key: Nat -> String
  for +n: Nat
  {F.length(candidates(key, n)) == 1n+n : Nat}
def candidate_count(key, n):
  match n:
    case 0n: {==}
    case 1n+k:
      Equal.cong(Nat, Nat, p => 1n+p, F.length(candidates(key, k)), 1n+k, candidate_count(key, k))

# Give the official lowering an explicitly typed equality parameter before
# dependent elimination. The equality is still derived by the real encoder
# inverse; this lemma assumes no injectivity or freshness conclusion.
def equal_indices_contradict_strict_order(+low: Nat, -high: Nat,
  strict: F.Le(1n+low, high), same: {high == low : Nat}) -> Empty:
  F.successor_cannot_be_bounded_by_itself(low,
    (%same : F.Le(1n+low, _) strict))

def strictly_ordered_keys_differ(+limit: Nat, +bound: B.Number64, +high: Nat, +low: Nat,
  represented: {B.nat64(limit) == Some{bound} : Maybe<&2, B.Number64>},
  high_bounded: {Nat.is_le(high, limit) == True{} : Bool},
  strict: F.Le(1n+low, high), same: {H.counter_key(high) == H.counter_key(low) : String}) -> Empty:
  equal_indices_contradict_strict_order(low, high, strict,
    H.counter_key_injective_bounded(limit, bound, high, low, represented, high_bounded, same))

law higher_counter_is_absent_from_lower_candidates:
  for +low: Nat
  for +high: Nat
  for +limit: Nat
  for +bound: B.Number64
  for +represented: {B.nat64(limit) == Some{bound} : Maybe<&2, B.Number64>}
  for +high_bounded: {Nat.is_le(high, limit) == True{} : Bool}
  for +strict: F.Le(1n+low, high)
  F.Absent(H.counter_key(high), candidates(H.counter_key, low))
def higher_counter_is_absent_from_lower_candidates(low, high, limit, bound, represented, high_bounded, strict):
  match low:
    case 0n:
      L.Both{same => strictly_ordered_keys_differ(limit, bound, high, 0n, represented, high_bounded, strict, same), Unit{}}
    case 1n+k:
      L.Both{same => strictly_ordered_keys_differ(limit, bound, high, 1n+k, represented, high_bounded, strict, same),
        higher_counter_is_absent_from_lower_candidates(k, high, limit, bound, represented, high_bounded, F.le_weaken_successor(1n+k, high, strict))}

law bounded_counter_candidates_are_unique:
  for +n: Nat
  for +limit: Nat
  for +bound: B.Number64
  for +represented: {B.nat64(limit) == Some{bound} : Maybe<&2, B.Number64>}
  for +bounded: F.Le(n, limit)
  F.Unique(candidates(H.counter_key, n))
def bounded_counter_candidates_are_unique(n, limit, bound, represented, bounded):
  match n:
    case 0n: L.Both{Unit{}, Unit{}}
    case 1n+k:
      L.Both{higher_counter_is_absent_from_lower_candidates(k, 1n+k, limit, bound, represented, F.le_as_actual_boolean(1n+k, limit, bounded), F.le_reflexive(1n+k)),
        bounded_counter_candidates_are_unique(k, limit, bound, represented, F.le_weaken_successor(k, limit, bounded))}

law actual_bounded_counter_search_finds_fresh_key:
  for +keys: List<&2, String>
  for +bound: B.Number64
  for +represented: {B.nat64(F.length(keys)) == Some{bound} : Maybe<&2, B.Number64>}
  exs found: String
  L.E<{F.search(candidates(H.counter_key, F.length(keys)), keys) == Some{found} : Maybe<&2, String>},
    {F.member(found, keys) == False{} : Bool}>
def actual_bounded_counter_search_finds_fresh_key(keys, bound, represented):
  F.finite_fresh_search_from_real_cardinality(candidates(H.counter_key, F.length(keys)), keys,
    bounded_counter_candidates_are_unique(F.length(keys), F.length(keys), bound, represented, F.le_reflexive(F.length(keys))), candidate_count(H.counter_key, F.length(keys)))

# Same bounded descending counter loop as the native allocator, producing
# candidates on demand instead of materializing the proof's finite list.
def search_counter(~key: Nat -> String, +counter: Nat,
  +keys: List<&2, String>) -> Maybe<&2, String>:
  match counter:
    case 0n: F.search_member(F.member(key(0n), keys), key(0n), None{})
    case 1n+k:
      F.search_member(F.member(key(1n+k), keys), key(1n+k), search_counter(key, k, keys))

law generated_loop_is_the_finite_search:
  for ~key: Nat -> String
  for +counter: Nat
  for +keys: List<&2, String>
  {search_counter(key, counter, keys) == F.search(candidates(key, counter), keys) : Maybe<&2, String>}
def generated_loop_is_the_finite_search(key, counter, keys):
  match counter:
    case 0n: {==}
    case 1n+k:
      Equal.cong(Maybe<&2, String>, Maybe<&2, String>,
        later => F.search_member(F.member(key(1n+k), keys), key(1n+k), later),
        search_counter(key, k, keys), F.search(candidates(key, k), keys),
        generated_loop_is_the_finite_search(key, k, keys))

def loop_result_from_finite(~key: Nat -> String, +keys: List<&2, String>,
  found: &value: String ->
    L.E<{F.search(candidates(key, F.length(keys)), keys) == Some{value} : Maybe<&2, String>},
      {F.member(value, keys) == False{} : Bool}>) ->
  &value: String ->
    L.E<{search_counter(key, F.length(keys), keys) == Some{value} : Maybe<&2, String>},
      {F.member(value, keys) == False{} : Bool}>:
  (value, L.Both{exact, absent}) = found
  (value, L.Both{Equal.trans(Maybe<&2, String>, search_counter(key, F.length(keys), keys),
    F.search(candidates(key, F.length(keys)), keys), Some{value},
    generated_loop_is_the_finite_search(key, F.length(keys), keys), exact), absent})

law actual_bounded_loop_finds_fresh_key:
  for +keys: List<&2, String>
  for +bound: B.Number64
  for +represented: {B.nat64(F.length(keys)) == Some{bound} : Maybe<&2, B.Number64>}
  exs found: String
  L.E<{search_counter(H.counter_key, F.length(keys), keys) == Some{found} : Maybe<&2, String>},
    {F.member(found, keys) == False{} : Bool}>
def actual_bounded_loop_finds_fresh_key(keys, bound, represented):
  loop_result_from_finite(H.counter_key, keys,
    actual_bounded_counter_search_finds_fresh_key(keys, bound, represented))

def allocate(~key: Nat -> String, +random: String, +keys: List<&2, String>) -> Maybe<&2, String>:
  F.search_member(F.member(random, keys), random, search_counter(key, F.length(keys), keys))

def allocation_case(~key: Nat -> String, found: Bool, +random: String,
  +keys: List<&2, String>, checked: {F.member(random, keys) == found : Bool},
  fallback: &value: String ->
    L.E<{search_counter(key, F.length(keys), keys) == Some{value} : Maybe<&2, String>},
      {F.member(value, keys) == False{} : Bool}>) ->
  &value: String ->
    L.E<{F.search_member(found, random, search_counter(key, F.length(keys), keys)) == Some{value} : Maybe<&2, String>},
      {F.member(value, keys) == False{} : Bool}>:
  match found:
    case False{}: (random, L.Both{{==}, checked})
    case True{}: fallback

law entropy_candidate_or_finite_fallback_always_finds_fresh_key:
  for +random: String
  for +keys: List<&2, String>
  for +bound: B.Number64
  for +represented: {B.nat64(F.length(keys)) == Some{bound} : Maybe<&2, B.Number64>}
  exs found: String
  L.E<{allocate(H.counter_key, random, keys) == Some{found} : Maybe<&2, String>},
    {F.member(found, keys) == False{} : Bool}>
def entropy_candidate_or_finite_fallback_always_finds_fresh_key(random, keys, bound, represented):
  allocation_case(H.counter_key, F.member(random, keys), random, keys, {==},
    actual_bounded_loop_finds_fresh_key(keys, bound, represented))

law equivalent_encoders_preserve_counter_loop:
  for ~left: Nat -> String
  for ~right: Nat -> String
  for ~same: @n: Nat -> {left(n) == right(n) : String}
  for +counter: Nat
  for +keys: List<&2, String>
  {search_counter(left, counter, keys) == search_counter(right, counter, keys) : Maybe<&2, String>}
def equivalent_encoders_preserve_counter_loop(left, right, same, counter, keys):
  match counter:
    case 0n:
      Equal.cong(String, Maybe<&2, String>, key => F.search_member(F.member(key, keys), key, None{}),
        left(0n), right(0n), same(0n))
    case 1n+k:
      Equal.trans(Maybe<&2, String>, search_counter(left, 1n+k, keys),
        F.search_member(F.member(right(1n+k), keys), right(1n+k), search_counter(left, k, keys)),
        search_counter(right, 1n+k, keys),
        Equal.cong(String, Maybe<&2, String>, key =>
          F.search_member(F.member(key, keys), key, search_counter(left, k, keys)),
          left(1n+k), right(1n+k), same(1n+k)),
        Equal.cong(Maybe<&2, String>, Maybe<&2, String>, later =>
          F.search_member(F.member(right(1n+k), keys), right(1n+k), later),
          search_counter(left, k, keys), search_counter(right, k, keys),
          equivalent_encoders_preserve_counter_loop(left, right, same, k, keys)))

law equivalent_encoders_preserve_allocator:
  for ~left: Nat -> String
  for ~right: Nat -> String
  for ~same: @n: Nat -> {left(n) == right(n) : String}
  for +random: String
  for +keys: List<&2, String>
  {allocate(left, random, keys) == allocate(right, random, keys) : Maybe<&2, String>}
def equivalent_encoders_preserve_allocator(left, right, same, random, keys):
  Equal.cong(Maybe<&2, String>, Maybe<&2, String>, later =>
    F.search_member(F.member(random, keys), random, later),
    search_counter(left, F.length(keys), keys), search_counter(right, F.length(keys), keys),
    equivalent_encoders_preserve_counter_loop(left, right, same, F.length(keys), keys))
