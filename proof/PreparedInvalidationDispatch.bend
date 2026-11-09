# Complete invalidation model: actual current authentication, proof-field
# validation, instance-scoped lookup, bounded receipt, removal, then cleanup.
# Rust/process correspondence is separate; no observer is manufactured here.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedProtocol.bend as W
import ../contract/PreparedRegistry.bend as G
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./Foundations.bend as F
import ./Orders.bend as O
import ./Preparation.bend as Preparation
import ./PreparedControlDispatch.bend as C

# H.invalidate computes both the exact lookup and the response bound. Cleanup
# cannot restore a removed entry or alter an earlier error cause.
def after_proof(empty: Bool, c: S.Configuration, initial: D.State,
  instance: String, +before: List<&2, G.Entry>, raw: P.Request,
  cleanup_failed: Bool) -> H.ControlResult:
  match empty:
    case False{}: H.ControlResult{initial, before, H.Error{S.Input{}}}
    case True{}:
      H.cleanup_invalidation(cleanup_failed,
        H.invalidate(c, initial, instance, I.code(raw), before))

def after_authentication(authentication: Maybe<&2, D.Context>, c: S.Configuration,
  initial: D.State, instance: String, before: List<&2, G.Entry>, +raw: P.Request,
  cleanup_failed: Bool) -> H.ControlResult:
  match authentication:
    case None{}: H.ControlResult{initial, before, H.Error{S.Authentication{}}}
    case Some{context}:
      after_proof(String.eq(I.proof(raw), ""), c, initial, instance, before, raw, cleanup_failed)

def invalidate(c: S.Configuration, +initial: D.State, instance: String,
  before: List<&2, G.Entry>, +raw: P.Request, cleanup_failed: Bool) -> H.ControlResult:
  after_authentication(D.authenticate(initial, I.credential(raw)), c, initial,
    instance, before, raw, cleanup_failed)

# A cleanup fault has to identify the exact selected entry and physical call.
# Unknown handles, oversized receipts and invalid/auth-failed inputs never
# acquire a cleanup obligation, since those branches do not attempt cleanup.
def CleanupSelected(fits: Bool, failed: Bool, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  -c: S.Configuration, +initial: D.State, -input: X.Reception,
  -instance: String, -entry: G.Entry) -> Type:
  match fits failed:
    case False{} _: Unit
    case True{} False{}: Unit
    case True{} True{}:
      H.CleanupFailure(a, artifacts, native, instance, entry, world, c, initial, input, time)

def CleanupLookup(found: Maybe<&2, G.Entry>, failed: Bool, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  c: S.Configuration, +initial: D.State, -input: X.Reception,
  -instance: String) -> Type:
  match found:
    case None{}: Unit
    case Some{entry}:
      CleanupSelected(R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.InvalidatedReceipt{})), failed, a, artifacts, native,
        world, time, c, initial, input, instance, entry)

def CleanupAfterProof(empty: Bool, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, c: S.Configuration,
  +initial: D.State, -input: X.Reception, +instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request, failed: Bool) -> Type:
  match empty:
    case False{}: Unit
    case True{}:
      CleanupLookup(G.lookup(instance, I.code(raw), before), failed, a, artifacts,
        native, world, time, c, initial, input, instance)

def CleanupEvidence(authentication: Maybe<&2, D.Context>, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  c: S.Configuration, +initial: D.State, -input: X.Reception,
  instance: String, before: List<&2, G.Entry>, +raw: P.Request, failed: Bool) -> Type:
  match authentication:
    case None{}: Unit
    case Some{context}:
      CleanupAfterProof(String.eq(I.proof(raw), ""), a, artifacts, native,
        world, time, c, initial, input, instance, before, raw, failed)

# Boolean lookup matching is proved to bind the original handle literally.
def handle_from_match(+instance: String, +handle: String, entry: G.Entry,
  matched: {G.matches(instance, handle, entry) == True{} : Bool}) ->
  {handle == G.handle(entry) : String}:
  match entry:
    case G.Entry{ei, +eh, code, proof, read, seal}:
      O.string_equal(handle, eh,
        F.and_boolean_right(String.eq(instance, ei), String.eq(handle, eh), matched))

def current_invalidation_ready(-c: S.Configuration, +initial: D.State,
  -input: X.Reception, +instance: String, +before: List<&2, G.Entry>,
  +raw: P.Request, +entry: G.Entry, -context: D.Context,
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  proof_empty: {I.proof(raw) == "" : String},
  +present: {G.lookup(instance, I.code(raw), before) == Some{entry} : Maybe<&2, G.Entry>}) ->
  H.InvalidationReady(c, initial, input, instance, before, raw, entry, context):
  L.Both{received, L.Both{authenticated, L.Both{
    L.Both{handle_from_match(instance, I.code(raw), entry,
      G.lookup_binds_instance_and_handle(instance, I.code(raw), before, entry, present)),
      proof_empty}, present}}}

law error_cleanup_is_neutral:
  for failed: Bool
  for initial: D.State
  for before: List<&2, G.Entry>
  for status: S.Status
  {H.cleanup_invalidation(failed, H.ControlResult{initial, before, H.Error{status}}) ==
    H.ControlResult{initial, before, H.Error{status}} : H.ControlResult}
def error_cleanup_is_neutral(failed, initial, before, status):
  match failed:
    case False{}: {==}
    case True{}: {==}

def selected_result_correct(~c: S.Configuration, fits: Bool, failed: Bool,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, +initial: D.State, -input: X.Reception, +instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request, +entry: G.Entry, context: D.Context,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  proof_empty: {I.proof(raw) == "" : String},
  present: {G.lookup(instance, I.code(raw), before) == Some{entry} : Maybe<&2, G.Entry>},
  receipt_checked: {R.fits(R.limit_response(S.limits(c)),
    W.receipt_value(W.InvalidatedReceipt{})) == fits : Bool},
  cleanup: CleanupSelected(fits, failed, a, artifacts, native, world, time,
    c, initial, input, instance, entry)) ->
  C.ResultCorrect(H.cleanup_invalidation(failed,
      H.invalidate_fits(fits, initial, instance, I.code(raw), before)), W.Invalidate{},
    a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  match fits failed:
    case False{} _:
      %Equal.sym(H.ControlResult,
        H.cleanup_invalidation(failed, H.ControlResult{initial, before, H.Error{S.Limit{}}}),
        H.ControlResult{initial, before, H.Error{S.Limit{}}},
        error_cleanup_is_neutral(failed, initial, before, S.Limit{})) :
        C.ResultCorrect(_, W.Invalidate{}, a, artifacts, native, world, time,
          c, initial, input, instance, before, raw)
      C.fixed_result_correct(c, S.Limit{}, W.Invalidate{}, a, artifacts, native,
        world, time, initial, input, instance, before, raw, valid, Unit{},
        L.Both{L.Right{(entry, context, L.Both{{==}, L.Both{
          current_invalidation_ready(c, initial, input, instance, before, raw,
            entry, context, received, authenticated, proof_empty, present), receipt_checked}})}, {==}})
    case True{} False{}:
      L.Both{{==}, L.Both{receipt_checked, (entry, context, L.Both{{==}, L.Both{
        current_invalidation_ready(c, initial, input, instance, before, raw,
          entry, context, received, authenticated, proof_empty, present), {==}}})}}
    case True{} True{}:
      L.Both{{==}, L.Both{
        Preparation.errors_fixed_fit(S.Failure{}, S.limits(c),
          Preparation.limits_of_configuration(c, valid), Unit{}),
        L.Right{L.Right{(entry, context, L.Both{{==}, L.Both{
          current_invalidation_ready(c, initial, input, instance, before, raw,
            entry, context, received, authenticated, proof_empty, present),
          L.Both{receipt_checked, L.Both{cleanup, {==}}}}})}}}}

def lookup_result_correct(~c: S.Configuration, found: Maybe<&2, G.Entry>, failed: Bool,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, +initial: D.State, -input: X.Reception, +instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request, context: D.Context,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  proof_empty: {I.proof(raw) == "" : String},
  present: {G.lookup(instance, I.code(raw), before) == found : Maybe<&2, G.Entry>},
  cleanup: CleanupLookup(found, failed, a, artifacts, native, world, time,
    c, initial, input, instance)) ->
  C.ResultCorrect(H.cleanup_invalidation(failed,
      H.invalidate_found(found, c, initial, instance, I.code(raw), before)), W.Invalidate{},
    a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  match found:
    case None{}:
      %Equal.sym(H.ControlResult,
        H.cleanup_invalidation(failed, H.ControlResult{initial, before, H.Error{S.Failure{}}}),
        H.ControlResult{initial, before, H.Error{S.Failure{}}},
        error_cleanup_is_neutral(failed, initial, before, S.Failure{})) :
        C.ResultCorrect(_, W.Invalidate{}, a, artifacts, native, world, time,
          c, initial, input, instance, before, raw)
      C.fixed_result_correct(c, S.Failure{}, W.Invalidate{}, a, artifacts, native,
        world, time, initial, input, instance, before, raw, valid, Unit{},
        L.Left{(context, L.Both{Unit{}, L.Both{authenticated,
          L.Both{proof_empty, L.Both{present, {==}}}}})})
    case Some{entry}:
      selected_result_correct(c, R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.InvalidatedReceipt{})), failed, a, artifacts, native,
        world, time, initial, input, instance, before, raw, entry, context,
        valid, received, authenticated, proof_empty, present, {==}, cleanup)

def proof_result_correct(~c: S.Configuration, empty: Bool, failed: Bool,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, +initial: D.State, -input: X.Reception, +instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request, context: D.Context,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  proof_checked: {String.eq(I.proof(raw), "") == empty : Bool},
  cleanup: CleanupAfterProof(empty, a, artifacts, native, world, time,
    c, initial, input, instance, before, raw, failed)) ->
  C.ResultCorrect(after_proof(empty, c, initial, instance, before, raw, failed),
    W.Invalidate{}, a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  match empty:
    case False{}:
      C.fixed_result_correct(c, S.Input{}, W.Invalidate{}, a, artifacts, native,
        world, time, initial, input, instance, before, raw, valid, Unit{},
        (context, L.Both{Unit{}, L.Both{authenticated, L.Both{proof_checked, {==}}}}))
    case True{}:
      lookup_result_correct(c, G.lookup(instance, I.code(raw), before), failed,
        a, artifacts, native, world, time, initial, input, instance, before, raw,
        context, valid, received, authenticated,
        O.string_equal(I.proof(raw), "", proof_checked), {==}, cleanup)

def authentication_result_correct(~c: S.Configuration,
  authentication: Maybe<&2, D.Context>, failed: Bool,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, +initial: D.State, -input: X.Reception, +instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
  authentication_exact: {D.authenticate(initial, I.credential(raw)) == authentication : Maybe<&2, D.Context>},
  cleanup: CleanupEvidence(authentication, a, artifacts, native, world, time,
    c, initial, input, instance, before, raw, failed)) ->
  C.ResultCorrect(after_authentication(authentication, c, initial, instance, before, raw, failed),
    W.Invalidate{}, a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  match authentication:
    case None{}:
      C.fixed_result_correct(c, S.Authentication{}, W.Invalidate{}, a, artifacts, native,
        world, time, initial, input, instance, before, raw, valid, Unit{},
        L.Both{authentication_exact, {==}})
    case Some{context}:
      proof_result_correct(c, String.eq(I.proof(raw), ""), failed, a, artifacts, native,
        world, time, initial, input, instance, before, raw, context,
        valid, received, authentication_exact, {==}, cleanup)

law complete_invalidation_result:
  for ~c: S.Configuration
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for +initial: D.State
  for -input: X.Reception
  for +instance: String
  for +before: List<&2, G.Entry>
  for +raw: P.Request
  for failed: Bool
  for valid: {R.configuration_is_valid(c) == True{} : Bool}
  for received: W.Received(c, input, W.Extension{W.Invalidate{}, raw})
  for cleanup: CleanupEvidence(D.authenticate(initial, I.credential(raw)), a, artifacts,
    native, world, time, c, initial, input, instance, before, raw, failed)
  C.ResultCorrect(invalidate(c, initial, instance, before, raw, failed), W.Invalidate{},
    a, artifacts, native, world, time, c, initial, input, instance, before, raw)
def complete_invalidation_result(c, a, artifacts, native, world, time, initial,
  input, instance, before, raw, failed, valid, received, cleanup):
  authentication_result_correct(c, D.authenticate(initial, I.credential(raw)), failed,
    a, artifacts, native, world, time, initial, input, instance, before, raw,
    valid, received, {==}, cleanup)

def outcome_with_received_pair(~c: S.Configuration,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, +initial: D.State, -input: X.Reception, +instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request, +failed: Bool,
  -previous: List<&2, U32>, +valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: L.E<W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
    W.Received(c, input, W.Extension{W.Invalidate{}, raw})>,
  cleanup: CleanupEvidence(D.authenticate(initial, I.credential(raw)), a, artifacts,
    native, world, time, c, initial, input, instance, before, raw, failed)) ->
  &bytes: List<&2, U32> -> H.ControlOutcome(a, artifacts, native, world, c, initial,
    input, time, instance, before, W.Invalidate{}, raw,
    invalidate(c, initial, instance, before, raw, failed), previous, previous, bytes):
  L.Both{physical, logical} = received
  C.correct_result_has_control_outcome(c, W.Invalidate{}, a, artifacts, native,
    world, time, initial, input, instance, before, raw,
    invalidate(c, initial, instance, before, raw, failed), previous, valid, physical,
    complete_invalidation_result(c, a, artifacts, native, world, time, initial,
      input, instance, before, raw, failed, valid, logical, cleanup))

law complete_invalidation_control_outcome:
  for ~c: S.Configuration
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for +initial: D.State
  for -input: X.Reception
  for +instance: String
  for +before: List<&2, G.Entry>
  for +raw: P.Request
  for +failed: Bool
  for -previous: List<&2, U32>
  for valid: {R.configuration_is_valid(c) == True{} : Bool}
  for received: W.Received(c, input, W.Extension{W.Invalidate{}, raw})
  for cleanup: CleanupEvidence(D.authenticate(initial, I.credential(raw)), a, artifacts,
    native, world, time, c, initial, input, instance, before, raw, failed)
  exs bytes: List<&2, U32>
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time, instance,
    before, W.Invalidate{}, raw, invalidate(c, initial, instance, before, raw, failed),
    previous, previous, bytes)
def complete_invalidation_control_outcome(c, a, artifacts, native, world, time,
  initial, input, instance, before, raw, failed, previous, valid, received, cleanup):
  outcome_with_received_pair(c, a, artifacts, native, world, time, initial, input,
    instance, before, raw, failed, previous, valid,
    C.physical_reception_data_can_be_reused(c, input, W.Extension{W.Invalidate{}, raw}, received), cleanup)
