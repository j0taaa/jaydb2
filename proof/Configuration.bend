# Exact configuration checks, initialization packets and recovery decisions.
import Base
import ../contract/Data.bend as D
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

# The computed configuration check and seed-validity proof yield success and
# exact state bytes; encoding success is derived, not supplied as a premise.
law valid_configuration_and_state_initialize_with_exact_encoding:
  for ~c: S.Configuration
  for identity: String
  for +state: D.State
  for configured: {C.is_valid(c, identity) == True{} : Bool}
  for valid: R.Valid(c, state)
  exs bytes: List<&2, U32>
  L.E<{P.encode(D.state_value(state)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    {C.initialize(c, identity, u => state) == Con{1, bytes} : List<&2, U32>}>
def valid_configuration_and_state_initialize_with_exact_encoding(c, identity, state, configured, valid):
  %Equal.sym(Bool, C.is_valid(c, identity), True{}, configured) :
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
  for identity: String
  for c: S.Configuration
  for configured: {C.is_valid(c, identity) == True{} : Bool}
  {C.recover(c, identity) == [1] : List<&2, U32>}
def valid_configuration_accepts_recovery_without_a_seed(identity, c, configured):
  %Equal.sym(Bool, C.is_valid(c, identity), True{}, configured) :
    {C.recovery_packet(_) == [1] : List<&2, U32>}
  {==}
