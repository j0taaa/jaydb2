# Consequences of the contract, with complete Bend proofs.
# Receiving `c: Contract(a,k)` does not prove that contract: these theorems
# state what can be concluded AFTER it has been proved for k.
import Base
import ./Logic.bend as L
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Interface.bend as I
import ./LAWS.bend as Laws

def obtain_law5(-a: I.Environment, -k: String, c: Laws.Contract(a, k)) -> Laws.Law5(a, k):
  match c:
    case L.Both{l1, L.Both{l2, L.Both{l3, L.Both{l4, L.Both{l5, rest}}}}}:
      l5

def obtain_law6(-a: I.Environment, -k: String, c: Laws.Contract(a, k)) -> Laws.Law6(a, k):
  match c:
    case L.Both{l1, L.Both{l2, L.Both{l3, L.Both{l4, L.Both{l5, L.Both{l6, rest}}}}}}:
      l6

law inspection_outside_of_model_impossible:
  for -a: I.Environment
  for -k: String
  for contract: Laws.Contract(a, k)
  for x: I.Scenario
  for t: Nat
  for description: String
  for occurred: I.Happens(a, k, x, t, I.InspectionNotModeled{description})
  Empty

def inspection_outside_of_model_impossible(a, k, contract, x, t, description, occurred):
  obtain_law5(a, k, contract)(x, t, I.InspectionNotModeled{description}, occurred)

def validity_of_publication(-a: I.Environment, -k: String, -x: I.Scenario,
  -t: Nat, -s: D.State, rule: Laws.Rule6(I.Published{s}, a, k, x, t)) -> R.Valid(I.configuration(x), s):
  match rule:
    case L.Both{valid, rest}:
      valid

law all_publication_and_is_valid:
  for -a: I.Environment
  for -k: String
  for contract: Laws.Contract(a, k)
  for x: I.Scenario
  for t: Nat
  for state: D.State
  for occurred: I.Happens(a, k, x, t, I.Published{state})
  R.Valid(I.configuration(x), state)

def all_publication_and_is_valid(a, k, contract, x, t, state, occurred):
  validity_of_publication(a, k, x, t, state,
    obtain_law6(a, k, contract)(x, t, I.Published{state}, occurred))

law refusal_native_preserves_state:
  for -a: I.Environment
  for -k: String
  for contract: Laws.Contract(a, k)
  for x: I.Scenario
  for t: Nat
  for value: D.Value
  for published: D.State
  for closes: Bool
  for occurred: I.Happens(a, k, x, t, I.Concluded{S.Response{S.Refusal{}, value}, published, closes})
  L.E<{published == I.initial(x) : D.State}, Laws.NonePublication(a, k, x)>

def refusal_native_preserves_state(a, k, contract, x, t, value, published, closes, occurred):
  obtain_law6(a, k, contract)(x, t, I.Concluded{S.Response{S.Refusal{}, value}, published, closes}, occurred)

law error_negative_erases_events:
  for -e: D.Schema
  for -s: D.State
  for -ts: List<&2, S.OperationEvent>
  for -o: D.Operation
  {S.resume_execution_trace(0n, S.OperationFailed{s, S.OperationEvent{o, S.ErrorOfData{}}}, e, ts) ==
    S.Final{s, S.append(ts, S.OperationEvent{o, S.ErrorOfData{}}),
      S.Response{S.DataError{}, D.VAbsent{}}} : S.Trace}

def error_negative_erases_events(e, s, ts, o):
  {==}
