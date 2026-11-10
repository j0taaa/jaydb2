# Concrete total allocator: one entropy candidate, then len..0 canonical hex.
# Fresh existence follows from actual membership and finite cardinality; no
# random-fairness or assumed fresh/injective-generator premise remains.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../contract/PreparedHandles.bend as Contract
import ./Foundations.bend as Foundations
import ./CodecSums64.bend as C64
import ./HandleCardinality.bend as F
import ./HandleCounters.bend as C
import ./HandleHex.bend as H

def allocate(+random: String, +keys: List<&2, String>) -> Maybe<&2, String>:
  C.allocate(H.counter_key, random, keys)

law allocator_always_terminates_with_fresh_key:
  for +random: String
  for +keys: List<&2, String>
  for +maximum: B.Number64
  for represented: {B.nat64(F.length(keys)) == Some{maximum} : Maybe<&2, B.Number64>}
  exs found: String
  L.E<{allocate(random, keys) == Some{found} : Maybe<&2, String>},
    {F.member(found, keys) == False{} : Bool}>
def allocator_always_terminates_with_fresh_key(random, keys, maximum, represented):
  C.entropy_candidate_or_finite_fallback_always_finds_fresh_key(random, keys, maximum, represented)

def ValidCandidates(keys: List<&2, String>) -> Type:
  match keys:
    case Nil{}: Unit
    case Con{head, rest}: L.E<H.ValidHandle(head), ValidCandidates(rest)>

law generated_counter_candidates_have_valid_shape:
  for +n: Nat
  for +limit: Nat
  for +maximum: B.Number64
  for +represented: {B.nat64(limit) == Some{maximum} : Maybe<&2, B.Number64>}
  for +bounded: F.Le(n, limit)
  ValidCandidates(C.candidates(H.counter_key, n))
def generated_counter_candidates_have_valid_shape(n, limit, maximum, represented, bounded):
  match n:
    case 0n:
      L.Both{H.counter_key_valid_bounded(limit, maximum, 0n, represented,
        F.le_as_actual_boolean(0n, limit, bounded)), Unit{}}
    case 1n+k:
      L.Both{H.counter_key_valid_bounded(limit, maximum, 1n+k, represented,
          F.le_as_actual_boolean(1n+k, limit, bounded)),
        generated_counter_candidates_have_valid_shape(k, limit, maximum, represented,
          F.le_weaken_successor(k, limit, bounded))}

law actual_candidate_recovers_valid_shape:
  for +keys: List<&2, String>
  for +value: String
  for valid: ValidCandidates(keys)
  for present: F.Has(value, keys)
  H.ValidHandle(value)
def actual_candidate_recovers_valid_shape(keys, value, valid, present):
  match keys valid present:
    case Nil{} _ impossible: match impossible:
    case Con{+head, rest} L.Both{head_valid, tail_valid} L.Left{same}:
      %Equal.sym(String, value, head, same) : H.ValidHandle(_)
      head_valid
    case Con{head, rest} L.Both{head_valid, tail_valid} L.Right{later}:
      actual_candidate_recovers_valid_shape(rest, value, tail_valid, later)

def selected_shape(found: Bool, +random: String, +keys: List<&2, String>, +value: String,
  +maximum: B.Number64,
  represented: {B.nat64(F.length(keys)) == Some{maximum} : Maybe<&2, B.Number64>},
  random_valid: H.ValidHandle(random),
  exact: {F.search_member(found, random, C.search_counter(H.counter_key, F.length(keys), keys)) == Some{value} : Maybe<&2, String>}) ->
  H.ValidHandle(value):
  match found:
    case False{}:
      %Foundations.some_injective(String, random, value, exact) : H.ValidHandle(_)
      random_valid
    case True{}:
      actual_candidate_recovers_valid_shape(C.candidates(H.counter_key, F.length(keys)), value,
        generated_counter_candidates_have_valid_shape(F.length(keys), F.length(keys), maximum,
          represented, F.le_reflexive(F.length(keys))),
        F.returned_search_value_is_an_actual_candidate(C.candidates(H.counter_key, F.length(keys)), keys, value,
          Equal.trans(Maybe<&2, String>, F.search(C.candidates(H.counter_key, F.length(keys)), keys),
            C.search_counter(H.counter_key, F.length(keys), keys), Some{value},
            Equal.sym(Maybe<&2, String>, C.search_counter(H.counter_key, F.length(keys), keys),
              F.search(C.candidates(H.counter_key, F.length(keys)), keys),
              C.generated_loop_is_the_finite_search(H.counter_key, F.length(keys), keys)), exact)))

law allocator_result_preserves_fixed_handle_format:
  for +random: String
  for +keys: List<&2, String>
  for +value: String
  for +maximum: B.Number64
  for represented: {B.nat64(F.length(keys)) == Some{maximum} : Maybe<&2, B.Number64>}
  for random_valid: H.ValidHandle(random)
  for exact: {allocate(random, keys) == Some{value} : Maybe<&2, String>}
  H.ValidHandle(value)
def allocator_result_preserves_fixed_handle_format(random, keys, value, maximum,
  represented, random_valid, exact):
  selected_shape(F.member(random, keys), random, keys, value, maximum,
    represented, random_valid, exact)

# Exactly the native [u8;32] entropy domain, converted to the same big-endian
# byte order before the shared two-nibble encoder. No entropy fairness needed.
def entropy_bytes(word: Word(256n)) -> List<&2, Word(8n)>:
  H.reverse(H.split_bytes(32n, word))

def entropy_handle(word: Word(256n)) -> String:
  H.encode_bytes(entropy_bytes(word))

law entropy_bytes_have_fixed_count:
  for +word: Word(256n)
  {H.count(entropy_bytes(word)) == 32n : Nat}
def entropy_bytes_have_fixed_count(word):
  Equal.trans(Nat, H.count(entropy_bytes(word)), H.count(H.split_bytes(32n, word)), 32n,
    H.count_reverse(H.split_bytes(32n, word)), H.count_split(32n, word))

law encoded_entropy_has_fixed_handle_shape:
  for +word: Word(256n)
  H.ValidHandle(entropy_handle(word))
def encoded_entropy_has_fixed_handle_shape(word):
  L.Both{Equal.trans(Nat, String.length(entropy_handle(word)),
      Nat.double(H.count(entropy_bytes(word))), 64n, H.encoded_length(entropy_bytes(word)),
      Equal.cong(Nat, Nat, Nat.double, H.count(entropy_bytes(word)), 32n,
        entropy_bytes_have_fixed_count(word))), H.encoded_lowercase(entropy_bytes(word))}

def complete_result(+random: String, +keys: List<&2, String>, +maximum: B.Number64,
  represented: {B.nat64(F.length(keys)) == Some{maximum} : Maybe<&2, B.Number64>},
  valid: H.ValidHandle(random),
  fresh: &value: String -> L.E<{allocate(random, keys) == Some{value} : Maybe<&2, String>},
    {F.member(value, keys) == False{} : Bool}>) ->
  &value: String -> L.E<{allocate(random, keys) == Some{value} : Maybe<&2, String>},
    L.E<{F.member(value, keys) == False{} : Bool},
      L.E<F.Absent(value, keys), Contract.HandleValid(value)>>>:
  (+value, L.Both{+exact, +absent}) = fresh
  (value, L.Both{exact, L.Both{absent,
    L.Both{F.actual_failed_membership_establishes_literal_absence(keys, value, absent),
      H.handle_contract(value,
        allocator_result_preserves_fixed_handle_format(random, keys, value, maximum, represented, valid, exact))}}})

def allocate_entropy(+word: Word(256n), keys: List<&2, String>) -> Maybe<&2, String>:
  allocate(entropy_handle(word), keys)

law concrete_allocator_is_total_fresh_and_contract_valid:
  for +word: Word(256n)
  for +keys: List<&2, String>
  for +maximum: B.Number64
  for +represented: {B.nat64(F.length(keys)) == Some{maximum} : Maybe<&2, B.Number64>}
  exs found: String
  L.E<{allocate_entropy(word, keys) == Some{found} : Maybe<&2, String>},
    L.E<{F.member(found, keys) == False{} : Bool},
      L.E<F.Absent(found, keys), Contract.HandleValid(found)>>>
def concrete_allocator_is_total_fresh_and_contract_valid(word, keys, maximum, represented):
  complete_result(entropy_handle(word), keys, maximum, represented,
    encoded_entropy_has_fixed_handle_shape(word),
    allocator_always_terminates_with_fresh_key(entropy_handle(word), keys, maximum, represented))

# Exact native byte construction, including its zero prefix, feeds the same
# byte encoder used for entropy. Its equivalence is proved candidate by
# candidate, then lifted through the actual descending loop.
def native_number_key(number: B.Number64) -> String:
  H.encode_bytes(H.counter_bytes(C64.bits(number)))

def native_optional_key(number: Maybe<&2, B.Number64>) -> String:
  match number:
    case None{}: ""
    case Some{number}: native_number_key(number)

def native_key(n: Nat) -> String:
  native_optional_key(B.nat64(n))

law native_optional_encoder_is_original:
  for number: Maybe<&2, B.Number64>
  {native_optional_key(number) == H.optional_key(number) : String}
def native_optional_encoder_is_original(number):
  match number:
    case None{}: {==}
    case Some{number}: H.counter_bytes_encoding(C64.bits(number))

law native_key_is_original:
  for n: Nat
  {native_key(n) == H.counter_key(n) : String}
def native_key_is_original(n):
  native_optional_encoder_is_original(B.nat64(n))

def native_allocate(+word: Word(256n), keys: List<&2, String>) -> Maybe<&2, String>:
  C.allocate(native_key, entropy_handle(word), keys)

law native_allocator_is_proved_allocator:
  for +word: Word(256n)
  for +keys: List<&2, String>
  {native_allocate(word, keys) == allocate_entropy(word, keys) : Maybe<&2, String>}
def native_allocator_is_proved_allocator(word, keys):
  C.equivalent_encoders_preserve_allocator(native_key, H.counter_key,
    n => native_key_is_original(n), entropy_handle(word), keys)

def native_result(+word: Word(256n), +keys: List<&2, String>,
  proved: &value: String -> L.E<{allocate_entropy(word, keys) == Some{value} : Maybe<&2, String>},
    L.E<{F.member(value, keys) == False{} : Bool},
      L.E<F.Absent(value, keys), Contract.HandleValid(value)>>>) ->
  &value: String -> L.E<{native_allocate(word, keys) == Some{value} : Maybe<&2, String>},
    L.E<{F.member(value, keys) == False{} : Bool},
      L.E<F.Absent(value, keys), Contract.HandleValid(value)>>>:
  (value, L.Both{exact, correct}) = proved
  (value, L.Both{Equal.trans(Maybe<&2, String>, native_allocate(word, keys),
    allocate_entropy(word, keys), Some{value}, native_allocator_is_proved_allocator(word, keys), exact), correct})

law native_allocator_is_total_fresh_and_contract_valid:
  for +word: Word(256n)
  for +keys: List<&2, String>
  for +maximum: B.Number64
  for represented: {B.nat64(F.length(keys)) == Some{maximum} : Maybe<&2, B.Number64>}
  exs found: String
  L.E<{native_allocate(word, keys) == Some{found} : Maybe<&2, String>},
    L.E<{F.member(found, keys) == False{} : Bool},
      L.E<F.Absent(found, keys), Contract.HandleValid(found)>>>
def native_allocator_is_total_fresh_and_contract_valid(word, keys, maximum, represented):
  native_result(word, keys,
    concrete_allocator_is_total_fresh_and_contract_valid(word, keys, maximum, represented))
