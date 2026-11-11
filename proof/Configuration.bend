# Exact configuration checks, initialization packets and recovery decisions.
import Base
import ../contract/Theorems.bend as T
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

# A success marker cannot equal the refusal marker. This observes actual
# returned bytes, independently of configuration and seed proof admission.
def success_marker(bytes: List<&2, U32>) -> Bool:
  match bytes:
    case Con{tag, rest}: U32.is_eq(tag, 1)
    case Nil{}: False{}

def success_not_refusal(-bytes: List<&2, U32>,
  same: {[2] == Con{1, bytes} : List<&2, U32>}) -> Empty:
  F.false_negative_true(Equal.cong(List<&2, U32>, Bool, success_marker, [2], Con{1, bytes}, same))

def packet_tail(bytes: List<&2, U32>) -> List<&2, U32>:
  match bytes:
    case Nil{}: Nil{}
    case Con{tag, rest}: rest

def packet_encoding(encoded: Maybe<&2, List<&2, U32>>, +bytes: List<&2, U32>,
  packet: {C.initial_packet(encoded) == Con{1, bytes} : List<&2, U32>}) ->
  {encoded == Some{bytes} : Maybe<&2, List<&2, U32>>}:
  match encoded:
    case None{}:
      L.ex_false({None{} == Some{bytes} : Maybe<&2, List<&2, U32>>}, success_not_refusal(bytes, packet))
    case Some{+actual}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, bs => Some{packet_tail(bs)},
        Con{1, actual}, Con{1, bytes}, packet)

def startup_success(accepted: Bool, -c: S.Configuration, -identity: String, +seed: D.State, +bytes: List<&2, U32>,
  configured: {C.is_valid(c, identity) == accepted : Bool},
  packet: {C.initialize_checked(accepted, u => seed) == Con{1, bytes} : List<&2, U32>}) ->
  L.E<{C.is_valid(c, identity) == True{} : Bool},
    {P.encode(D.state_value(seed)) == Some{bytes} : Maybe<&2, List<&2, U32>>}>:
  match accepted:
    case False{}:
      L.ex_false(L.E<{C.is_valid(c, identity) == True{} : Bool},
        {P.encode(D.state_value(seed)) == Some{bytes} : Maybe<&2, List<&2, U32>>}>, success_not_refusal(bytes, packet))
    case True{}: L.Both{configured, packet_encoding(P.encode(D.state_value(seed)), bytes, packet)}

def recovery_success(accepted: Bool, proof: {C.recovery_packet(accepted) == [1] : List<&2, U32>}) ->
  {accepted == True{} : Bool}:
  match accepted:
    case True{}: {==}
    case False{}: L.ex_false({False{} == True{} : Bool}, success_not_refusal(Nil{}, proof))

# The validity premise is the admitted declaration checked by assertInitialization.
# Neither initialize nor recover receives or evaluates proof evidence at runtime.
def startup_valid(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String,
  +identity: String, +seed: D.State,
  configured: {C.is_valid(S.Configuration{schema, laws, limits, instance}, identity) == True{} : Bool},
  valid: R.Valid(S.Configuration{schema, laws, limits, instance}, seed)) ->
  &bytes: List<&2, U32> ->
    L.E<{P.encode(D.state_value(seed)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
      {C.initialize(S.Configuration{schema, laws, limits, instance}, identity, u => seed) == Con{1, bytes} : List<&2, U32>}>:
  %Equal.sym(Bool, C.is_valid(S.Configuration{schema, S.NoneLaw{}, limits, instance}, identity), True{}, configured) :
    (&bytes: List<&2, U32> ->
      L.E<{P.encode(D.state_value(seed)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
        {C.initialize_checked(_, u => seed) == Con{1, bytes} : List<&2, U32>}>)
  bounded_initial_packet(P.encode(D.state_value(seed)), R.limit_state(limits),
    F.and_boolean_right(D.structure(schema, seed), R.fits(R.limit_state(limits), D.state_value(seed)),
      L.and_left({R.structure(S.Configuration{schema, laws, limits, instance}, seed) == True{} : Bool},
        S.Satisfies(S.Configuration{schema, laws, limits, instance}, S.Stable{seed}), valid)))

def startup_configuration(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String,
  +identity: String, +seed: D.State, valid: R.Valid(S.Configuration{schema, laws, limits, instance}, seed)) ->
  T.Startup(S.Configuration{schema, laws, limits, instance}, identity, seed):
  L.Both{configured => startup_valid(schema, laws, limits, instance, identity, seed, configured, valid),
    L.Both{+bytes => packet => startup_success(C.is_valid(S.Configuration{schema, S.NoneLaw{}, limits, instance}, identity), S.Configuration{schema, laws, limits, instance}, identity, seed, bytes, {==}, packet),
      L.Both{rejected => invalid_configuration_refuses_initialization(S.Configuration{schema, laws, limits, instance}, identity, u => seed, rejected),
        L.Both{proof => recovery_success(C.is_valid(S.Configuration{schema, S.NoneLaw{}, limits, instance}, identity), proof),
          configured => valid_configuration_accepts_recovery_without_a_seed(identity, S.Configuration{schema, S.NoneLaw{}, limits, instance}, configured)}}}}

def startup_config(c: S.Configuration, identity: String, seed: D.State, valid: R.Valid(c, seed)) ->
  T.Startup(c, identity, seed):
  match c:
    case S.Configuration{schema, laws, limits, instance}:
      startup_configuration(schema, laws, limits, instance, identity, seed, valid)

def startup_theorem() -> T.StartupTheorem():
  c => identity => seed => valid => startup_config(c, identity, seed, valid)
