# Deterministic invalidation selection from ACTUAL authentication and proof
# comparisons. No arbitrary Unchanged command can justify a return here.
# Physical decoder/host simulation and cleanup-IO provenance remain explicit.
import Base
import ../contract/Data.bend as D
import ../contract/RequestFacts.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedProtocol.bend as W
import ../contract/PreparedRegistry.bend as G
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./Orders.bend as O
import ./PreparedInvalidationDispatch.bend as V
import ./SourceService.bend as Source
import ./HostTransitions.bend as Host

type Choice is Data:
  Unauthenticated{}
  BadProof{context: D.Context}
  Selected{context: D.Context}

def choose_proof(empty: Bool, context: D.Context) -> Choice:
  match empty:
    case False{}: BadProof{context}
    case True{}: Selected{context}

def choose_auth(authentication: Maybe<&2, D.Context>, raw: P.Request) -> Choice:
  match authentication:
    case None{}: Unauthenticated{}
    case Some{context}: choose_proof(String.eq(I.proof(raw), ""), context)

def choose(+before: Host.Published, +raw: P.Request) -> Choice:
  choose_auth(D.authenticate(Host.database(before), I.credential(raw)), raw)

def invocation(+before: Host.Published, world: Nat, input: X.Reception,
  raw: P.Request, context: D.Context, failed: Bool) -> Host.Invocation:
  Host.Invocation{world, Host.database(before), input, Host.Invalidate{raw, context, failed}}

def Correct(~c: S.Configuration, +instance: String, +before: Host.Published,
  +world: Nat, +input: X.Reception, +raw: P.Request, +failed: Bool, choice: Choice) -> Type:
  match choice:
    case Unauthenticated{}:
      {D.authenticate(Host.database(before), I.credential(raw)) == None{} : Maybe<&2, D.Context>}
    case BadProof{context}:
      L.E<{D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
        {String.eq(I.proof(raw), "") == False{} : Bool}>
    case Selected{context}: Host.Step(c, instance, before, invocation(before, world, input, raw, context, failed))

def correct_proof(~c: S.Configuration, +instance: String, +before: Host.Published,
  +world: Nat, +input: X.Reception, +raw: P.Request, +failed: Bool, +context: D.Context, empty: Bool,
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
  authenticated: {D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  checked: {String.eq(I.proof(raw), "") == empty : Bool}) ->
  Correct(c, instance, before, world, input, raw, failed, choose_proof(empty, context)):
  match empty:
    case False{}: L.Both{authenticated, checked}
    case True{}: L.Both{{==}, L.Both{received, L.Both{authenticated, O.string_equal(I.proof(raw), "", checked)}}}

def correct_auth(~c: S.Configuration, +instance: String, +before: Host.Published,
  +world: Nat, +input: X.Reception, +raw: P.Request, +failed: Bool,
  authentication: Maybe<&2, D.Context>,
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
  checked: {D.authenticate(Host.database(before), I.credential(raw)) == authentication : Maybe<&2, D.Context>}) ->
  Correct(c, instance, before, world, input, raw, failed, choose_auth(authentication, raw)):
  match authentication:
    case None{}: checked
    case Some{context}:
      correct_proof(c, instance, before, world, input, raw, failed, context, String.eq(I.proof(raw), ""), received, checked, {==})

law deterministic_selection_has_only_concrete_rejection_or_authorized_operational_step:
  for ~c: S.Configuration
  for +instance: String
  for +before: Host.Published
  for +world: Nat
  for +input: X.Reception
  for +raw: P.Request
  for +failed: Bool
  for received: W.Received(c, input, W.Extension{W.Invalidate{}, raw})
  Correct(c, instance, before, world, input, raw, failed, choose(before, raw))
def deterministic_selection_has_only_concrete_rejection_or_authorized_operational_step(c, instance, before, world, input, raw, failed, received):
  correct_auth(c, instance, before, world, input, raw, failed,
    D.authenticate(Host.database(before), I.credential(raw)), received, {==})

def chosen_result(choice: Choice, c: S.Configuration, initial: D.State,
  instance: String, before: List<&2, G.Entry>, raw: P.Request, failed: Bool) -> H.ControlResult:
  match choice:
    case Unauthenticated{}: H.ControlResult{initial, before, H.Error{S.Authentication{}}}
    case BadProof{context}: H.ControlResult{initial, before, H.Error{S.Input{}}}
    case Selected{context}: H.cleanup_invalidation(failed, H.invalidate(c, initial, instance, I.code(raw), before))

def proof_result_exact(empty: Bool, c: S.Configuration, +initial: D.State,
  +instance: String, +before: List<&2, G.Entry>, +raw: P.Request, +failed: Bool, -context: D.Context) ->
  {V.after_proof(empty, c, initial, instance, before, raw, failed) ==
    chosen_result(choose_proof(empty, context), c, initial, instance, before, raw, failed) : H.ControlResult}:
  match empty:
    case False{}: {==}
    case True{}: {==}

def auth_result_exact(authentication: Maybe<&2, D.Context>, c: S.Configuration, +initial: D.State,
  +instance: String, +before: List<&2, G.Entry>, +raw: P.Request, +failed: Bool) ->
  {V.after_authentication(authentication, c, initial, instance, before, raw, failed) ==
    chosen_result(choose_auth(authentication, raw), c, initial, instance, before, raw, failed) : H.ControlResult}:
  match authentication:
    case None{}: {==}
    case Some{context}: proof_result_exact(String.eq(I.proof(raw), ""), c, initial, instance, before, raw, failed, context)

law deterministic_selection_returns_exact_complete_invalidation_result:
  for c: S.Configuration
  for +instance: String
  for +before: Host.Published
  for +raw: P.Request
  for +failed: Bool
  {V.invalidate(c, Host.database(before), instance, Host.entries(before), raw, failed) ==
    chosen_result(choose(before, raw), c, Host.database(before), instance, Host.entries(before), raw, failed) : H.ControlResult}
def deterministic_selection_returns_exact_complete_invalidation_result(c, instance, before, raw, failed):
  auth_result_exact(D.authenticate(Host.database(before), I.credential(raw)), c,
    Host.database(before), instance, Host.entries(before), raw, failed)

def chosen_pair_valid(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, ~book: Host.InputBook,
  +instance: String, before: Host.Published, choice: Choice, +raw: P.Request, +failed: Bool,
  valid: Host.Valid(c, binding, public, book, instance, before)) ->
  Host.Valid(c, binding, public, book, instance,
    Host.control(chosen_result(choice, c, Host.database(before), instance, Host.entries(before), raw, failed), Host.response(before))):
  match before choice:
    case Host.Published{state, previous, es} Unauthenticated{}: valid
    case Host.Published{state, previous, es} BadProof{context}: valid
    case Host.Published{+state, +previous, +es} Selected{context}:
      match valid:
        case L.Both{state_valid, origins}:
          %Equal.sym(Host.Published,
            Host.control(H.cleanup_invalidation(failed, H.invalidate(c, state, instance, I.code(raw), es)), previous),
            Host.control(H.invalidate(c, state, instance, I.code(raw), es), previous),
            Host.cleanup_keeps_complete_published_pair(failed, H.invalidate(c, state, instance, I.code(raw), es), previous)) :
              Host.Valid(c, binding, public, book, instance, _)
          Host.invalidate_found_valid(c, binding, public, book, instance, G.lookup(instance, I.code(raw), es),
            state, previous, I.code(raw), es, state_valid, origins)

law deterministic_invalidation_preserves_current_database_response_and_registered_origins:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for +instance: String
  for +before: Host.Published
  for +raw: P.Request
  for +failed: Bool
  for valid: Host.Valid(c, binding, public, book, instance, before)
  Host.Valid(c, binding, public, book, instance,
    Host.control(V.invalidate(c, Host.database(before), instance, Host.entries(before), raw, failed), Host.response(before)))
def deterministic_invalidation_preserves_current_database_response_and_registered_origins(c, binding, public, book, instance, before, raw, failed, valid):
  %Equal.sym(H.ControlResult,
    V.invalidate(c, Host.database(before), instance, Host.entries(before), raw, failed),
    chosen_result(choose(before, raw), c, Host.database(before), instance, Host.entries(before), raw, failed),
    deterministic_selection_returns_exact_complete_invalidation_result(c, instance, before, raw, failed)) :
      Host.Valid(c, binding, public, book, instance, Host.control(_, Host.response(before)))
  chosen_pair_valid(c, binding, public, book, instance, before, choose(before, raw), raw, failed, valid)
