# Links the initialization test to the original relation.
# Defines neither Environment, observes, Processable nor any host fact.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../src/ConfigurationCheck.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O

law accepts_requires_structure_and_identity_exact:
  for c: S.Configuration
  for +identity: String
  for accepted: {C.is_valid(c, identity) == True{} : Bool}
  L.E<{R.configuration_is_valid(c) == True{} : Bool},
    {S.environment(c) == identity : String}>
def accepts_requires_structure_and_identity_exact(c, identity, accepted):
  match c:
    case S.Configuration{e, ls, lim, +amb}:
      F.combined_pair(
        L.E<{R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) == True{} : Bool}, {amb == identity : String}>,
        {R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) == True{} : Bool},
        {String.eq(amb, identity) == True{} : Bool},
        F.and_boolean_separate(R.configuration_is_valid(S.Configuration{e, ls, lim, amb}), String.eq(amb, identity), accepted),
        structure => equal => L.Both{structure, O.string_equal(amb, identity, equal)})

law accepts_satisfies_configuration_is_valid_original:
  for a: I.Environment
  for c: S.Configuration
  for accepted: {C.is_valid(c, I.identity(a)) == True{} : Bool}
  I.ConfigurationValid(a, c)
def accepts_satisfies_configuration_is_valid_original(a, c, accepted):
  accepts_requires_structure_and_identity_exact(c, I.identity(a), accepted)

law configuration_original_is_valid_and_accepts:
  for a: I.Environment
  for c: S.Configuration
  for is_valid: I.ConfigurationValid(a, c)
  {C.is_valid(c, I.identity(a)) == True{} : Bool}
def configuration_original_is_valid_and_accepts(a, c, is_valid):
  match c:
    case S.Configuration{+e, ls, +lim, +amb}:
      +id = I.identity(a)
      F.combined_pair({C.is_valid(S.Configuration{e, ls, lim, amb}, id) == True{} : Bool},
        {R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) == True{} : Bool}, {amb == id : String}, is_valid,
        structure => equal => F.and_boolean_intro(R.configuration_is_valid(S.Configuration{e, ls, lim, amb}), String.eq(amb, id),
          structure, (%Equal.sym(String, amb, id, equal) :
            {String.eq(_, id) == True{} : Bool}
            O.string_eq_refl(id))))

# These are the pure functions called by the generated native entry points,
# rather than a second startup model. Compiler/IO and admission correspondence
# remain separate obligations; no initial-state validity is inferred here.
law invalid_configuration_refuses_initialization:
  for -c: S.Configuration
  for -identity: String
  for -seed: Unit -> D.State
  for rejected: {C.is_valid(c, identity) == False{} : Bool}
  {C.initialize(c, identity, seed) == [2] : List<&2, U32>}
def invalid_configuration_refuses_initialization(c, identity, seed, rejected):
  %Equal.sym(Bool, C.is_valid(c, identity), False{}, rejected) :
    {C.initialize_checked(_, seed) == [2] : List<&2, U32>}
  {==}

def bounded_initial_packet(encoded: Maybe<&2, List<&2, U32>>, -limit: Nat,
  fits: {R.fits_result(encoded, limit) == True{} : Bool}) ->
  &bytes: List<&2, U32> -> L.E<{encoded == Some{bytes} : Maybe<&2, List<&2, U32>>},
    {C.initial_packet(encoded) == Con{1, bytes} : List<&2, U32>}>:
  match encoded:
    case None{}:
      F.absurd_boolean((&bytes: List<&2, U32> -> L.E<{None{} == Some{bytes} : Maybe<&2, List<&2, U32>>},
        {C.initial_packet(None{}) == Con{1, bytes} : List<&2, U32>}>), fits)
    case Some{+bytes}: (bytes, L.Both{{==}, {==}})

def valid_state_initial_packet(c: S.Configuration, +state: D.State, valid: R.Valid(c, state)) ->
  &bytes: List<&2, U32> -> L.E<{P.encode(D.state_value(state)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    {C.initial_packet(P.encode(D.state_value(state))) == Con{1, bytes} : List<&2, U32>}>:
  match c:
    case S.Configuration{+e, ls, +limits, +identity}:
      bounded_initial_packet(P.encode(D.state_value(state)), R.limit_state(limits),
        F.and_boolean_right(D.structure(e, state), R.fits(R.limit_state(limits), D.state_value(state)),
          L.and_left({R.structure(S.Configuration{e, ls, limits, identity}, state) == True{} : Bool},
            S.Satisfies(S.Configuration{e, ls, limits, identity}, S.Stable{state}), valid)))

# The original configuration and seed-validity conditions yield success and
# exact state bytes; encoding success is derived, not supplied as a premise.
law valid_configuration_and_state_initialize_with_exact_encoding:
  for ~c: S.Configuration
  for a: I.Environment
  for +state: D.State
  for configured: I.ConfigurationValid(a, c)
  for valid: R.Valid(c, state)
  exs bytes: List<&2, U32>
  L.E<{P.encode(D.state_value(state)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    {C.initialize(c, I.identity(a), u => state) == Con{1, bytes} : List<&2, U32>}>
def valid_configuration_and_state_initialize_with_exact_encoding(c, a, state, configured, valid):
  %Equal.sym(Bool, C.is_valid(c, I.identity(a)), True{}, configuration_original_is_valid_and_accepts(a, c, configured)) :
    (&bytes: List<&2, U32> -> L.E<{P.encode(D.state_value(state)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
      {C.initialize_checked(_, u => state) == Con{1, bytes} : List<&2, U32>}>)
  valid_state_initial_packet(c, state, valid)

law invalid_configuration_refuses_recovery:
  for -c: S.Configuration
  for -identity: String
  for rejected: {C.is_valid(c, identity) == False{} : Bool}
  {C.recover(c, identity) == [2] : List<&2, U32>}
def invalid_configuration_refuses_recovery(c, identity, rejected):
  %Equal.sym(Bool, C.is_valid(c, identity), False{}, rejected) :
    {C.recovery_packet(_) == [2] : List<&2, U32>}
  {==}

law valid_configuration_accepts_recovery_without_a_seed:
  for a: I.Environment
  for c: S.Configuration
  for configured: I.ConfigurationValid(a, c)
  {C.recover(c, I.identity(a)) == [1] : List<&2, U32>}
def valid_configuration_accepts_recovery_without_a_seed(a, c, configured):
  %Equal.sym(Bool, C.is_valid(c, I.identity(a)), True{}, configuration_original_is_valid_and_accepts(a, c, configured)) :
    {C.recovery_packet(_) == [1] : List<&2, U32>}
  {==}
