# Physical prepared admission reaches the actual resolver and Core theorem.
# Control transitions below are the full contract functions, including lookup
# and receipt bounds. No final-state validity or publication permission is an
# input to the transaction theorem.
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
import ../src/Core.bend as N
import ../src/Prepared.bend as Prepared
import ./Call.bend as Call
import ./PreparedPrograms.bend as Programs

law resolved_matches_worker:
  for raw: P.Request
  for +entry: G.Entry
  {H.resolved(raw, entry) == Prepared.resolve_request(raw, G.code(entry), G.proof(entry)) : P.Request}
def resolved_matches_worker(raw, entry):
  match raw:
    case P.Request{credential, handle, arguments, unused}: {==}

def certificate_of_mode(mode: Bool, -a: I.Environment, -c: S.Configuration,
  -entry: G.Entry, -program: S.Program,
  certificate: H.ModeCertificateCases(mode, a, c, entry, program)) -> H.CertificateValid(a, c, entry, program):
  match mode:
    case False{}: certificate
    case True{}:
      match certificate:
        case L.Both{ordinary, read}: ordinary

law mode_certificate_implies_certificate:
  for -a: I.Environment
  for -c: S.Configuration
  for entry: G.Entry
  for -program: S.Program
  for certificate: H.ModeCertificateValid(a, c, entry, program)
  H.CertificateValid(a, c, entry, program)
def mode_certificate_implies_certificate(a, c, entry, program, certificate):
  certificate_of_mode(G.read_only(entry), a, c, entry, program, certificate)

def universal_of_certificate(-a: I.Environment, -c: S.Configuration,
  -entry: G.Entry, -program: S.Program,
  certificate: H.CertificateValid(a, c, entry, program)) -> Programs.Universal(c, G.code(entry), program):
  match certificate:
    case L.Both{bound, L.Both{derived, universal}}: universal

# The conclusion uses the original registered source and the actual current
# context/arguments. It asserts no concrete Derives judgment for universal text.
law ready_certifies_actual_call:
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for -c: S.Configuration
  for -state: D.State
  for -input: X.Reception
  for -instance: String
  for -entries: List<&2, G.Entry>
  for raw: P.Request
  for +entry: G.Entry
  for context: D.Context
  for -program: S.Program
  for ready: H.Ready(a, artifacts, native, world, time, c, state, input, instance, entries, raw, entry, context, program)
  R.Certifies(c, I.code(H.resolved(raw, entry)), program, context, I.arguments(H.resolved(raw, entry)))
def ready_certifies_actual_call(a, artifacts, native, world, time, c, state, input, instance, entries,
  raw, entry, context, program, ready):
  match raw:
    case P.Request{credential, handle, arguments, unused}:
      match ready:
        case L.Both{received, L.Both{authenticated, L.Both{fields, L.Both{lookup, L.Both{certificate, intact}}}}}:
          universal_of_certificate(a, c, entry, program,
            mode_certificate_implies_certificate(a, c, entry, program, certificate))(context, arguments)

law ready_resolution_retains_original_source_and_current_call:
  for raw: P.Request
  for +entry: G.Entry
  L.E<{I.code(H.resolved(raw, entry)) == G.code(entry) : String},
    L.E<{I.proof(H.resolved(raw, entry)) == G.proof(entry) : String},
      L.E<{I.credential(H.resolved(raw, entry)) == I.credential(raw) : String},
        {I.arguments(H.resolved(raw, entry)) == I.arguments(raw) : D.Value}>>>
def ready_resolution_retains_original_source_and_current_call(raw, entry):
  match raw:
    case P.Request{credential, handle, arguments, unused}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, {==}}}}

law ready_call_prepares_and_concludes:
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for c: S.Configuration
  for -input: X.Reception
  for -instance: String
  for -entries: List<&2, G.Entry>
  for raw: P.Request
  for +entry: G.Entry
  for +context: D.Context
  for program: S.Program
  for +state: D.State
  for ready: H.Ready(a, artifacts, native, world, time, c, state, input, instance, entries, raw, entry, context, program)
  for valid: R.Valid(c, state)
  for +n: Nat
  for +working: D.State
  for +events: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for execution: {N.traverse(n, N.start(program, context, I.arguments(raw), state), S.schema(c)) ==
    S.Final{working, events, proposal} : S.Trace}
  for configuration_valid: {R.configuration_is_valid(c) == True{} : Bool}
  Call.ConclusionIntegral(c, state, working, events, proposal)
def ready_call_prepares_and_concludes(a, artifacts, native, world, time, c, input, instance, entries,
  raw, entry, context, program, state, ready, valid, n, working, events, proposal, execution, configuration_valid):
  match ready:
    case L.Both{received, L.Both{authenticated, L.Both{fields, L.Both{lookup, L.Both{certificate, intact}}}}}:
      Programs.prepared_call_prepares_and_concludes(c, G.code(entry), program, context, raw,
        universal_of_certificate(a, c, entry, program,
          mode_certificate_implies_certificate(a, c, entry, program, certificate)),
        state, valid, authenticated, n, working, events, proposal, execution, configuration_valid)

def register_found_preserves_state(found: Maybe<&2, G.Entry>, c: S.Configuration,
  +initial: D.State, +entry: G.Entry, entries: List<&2, G.Entry>) ->
  {H.state(H.register_found(found, c, initial, entry, entries)) == initial : D.State}:
  match found:
    case Some{previous}: {==}
    case None{}:
      H.register_fit_stage_preserves_published_state(
        R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})), initial, entry, entries)

law registration_preserves_published_state:
  for c: S.Configuration
  for +initial: D.State
  for instance: String
  for +entry: G.Entry
  for +entries: List<&2, G.Entry>
  {H.state(H.register(c, initial, instance, entry, entries)) == initial : D.State}
def registration_preserves_published_state(c, initial, instance, entry, entries):
  register_found_preserves_state(G.lookup(instance, G.handle(entry), entries), c, initial, entry, entries)

def invalidate_found_preserves_state(found: Maybe<&2, G.Entry>, c: S.Configuration,
  +initial: D.State, instance: String, handle: String, entries: List<&2, G.Entry>) ->
  {H.state(H.invalidate_found(found, c, initial, instance, handle, entries)) == initial : D.State}:
  match found:
    case None{}: {==}
    case Some{entry}:
      H.invalidate_fit_stage_preserves_published_state(
        R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), initial, instance, handle, entries)

law invalidation_preserves_published_state:
  for c: S.Configuration
  for +initial: D.State
  for +instance: String
  for +handle: String
  for +entries: List<&2, G.Entry>
  {H.state(H.invalidate(c, initial, instance, handle, entries)) == initial : D.State}
def invalidation_preserves_published_state(c, initial, instance, handle, entries):
  invalidate_found_preserves_state(G.lookup(instance, handle, entries), c, initial, instance, handle, entries)

def oversized_register_found(found: Maybe<&2, G.Entry>, -c: S.Configuration,
  -initial: D.State, -entry: G.Entry, -entries: List<&2, G.Entry>,
  oversized: H.ReceiptTooLarge(c, W.PreparedReceipt{G.handle(entry)})) ->
  {H.registry(H.register_found(found, c, initial, entry, entries)) == entries : List<&2, G.Entry>}:
  match found:
    case Some{previous}: {==}
    case None{}:
      %Equal.sym(Bool, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})), False{}, oversized) :
        {H.registry(H.register_fits(_, initial, entry, entries)) == entries : List<&2, G.Entry>}
      {==}

law oversized_registration_receipt_preserves_registry:
  for -c: S.Configuration
  for -initial: D.State
  for instance: String
  for entry: G.Entry
  for entries: List<&2, G.Entry>
  for oversized: H.ReceiptTooLarge(c, W.PreparedReceipt{G.handle(entry)})
  {H.registry(H.register(c, initial, instance, entry, entries)) == entries : List<&2, G.Entry>}
def oversized_registration_receipt_preserves_registry(c, initial, instance, entry, entries, oversized):
  oversized_register_found(G.lookup(instance, G.handle(entry), entries), c, initial, entry, entries, oversized)

def oversized_invalidate_found(found: Maybe<&2, G.Entry>, -c: S.Configuration,
  -initial: D.State, -instance: String, -handle: String, -entries: List<&2, G.Entry>,
  oversized: H.ReceiptTooLarge(c, W.InvalidatedReceipt{})) ->
  {H.registry(H.invalidate_found(found, c, initial, instance, handle, entries)) == entries : List<&2, G.Entry>}:
  match found:
    case None{}: {==}
    case Some{entry}:
      %Equal.sym(Bool, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), False{}, oversized) :
        {H.registry(H.invalidate_fits(_, initial, instance, handle, entries)) == entries : List<&2, G.Entry>}
      {==}

law oversized_invalidation_receipt_preserves_registry:
  for -c: S.Configuration
  for -initial: D.State
  for instance: String
  for handle: String
  for entries: List<&2, G.Entry>
  for oversized: H.ReceiptTooLarge(c, W.InvalidatedReceipt{})
  {H.registry(H.invalidate(c, initial, instance, handle, entries)) == entries : List<&2, G.Entry>}
def oversized_invalidation_receipt_preserves_registry(c, initial, instance, handle, entries, oversized):
  oversized_invalidate_found(G.lookup(instance, handle, entries), c, initial, instance, handle, entries, oversized)

law fresh_fitting_registration_returns_receipt_and_exact_entry:
  for -c: S.Configuration
  for -initial: D.State
  for -instance: String
  for -entry: G.Entry
  for -entries: List<&2, G.Entry>
  for fresh: {G.lookup(instance, G.handle(entry), entries) == None{} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})) == True{} : Bool}
  {H.register(c, initial, instance, entry, entries) ==
    H.ControlResult{initial, Con{entry, entries}, H.Metadata{W.PreparedReceipt{G.handle(entry)}}} : H.ControlResult}
def fresh_fitting_registration_returns_receipt_and_exact_entry(c, initial, instance, entry, entries, fresh, fits):
  %Equal.sym(Maybe<&2, G.Entry>, G.lookup(instance, G.handle(entry), entries), None{}, fresh) :
    {H.register_found(_, c, initial, entry, entries) ==
      H.ControlResult{initial, Con{entry, entries}, H.Metadata{W.PreparedReceipt{G.handle(entry)}}} : H.ControlResult}
  %Equal.sym(Bool, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})), True{}, fits) :
    {H.register_fits(_, initial, entry, entries) ==
      H.ControlResult{initial, Con{entry, entries}, H.Metadata{W.PreparedReceipt{G.handle(entry)}}} : H.ControlResult}
  {==}

law known_fitting_invalidation_returns_receipt_and_removes_handle:
  for -c: S.Configuration
  for -initial: D.State
  for -instance: String
  for -handle: String
  for -entry: G.Entry
  for -entries: List<&2, G.Entry>
  for present: {G.lookup(instance, handle, entries) == Some{entry} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool}
  {H.invalidate(c, initial, instance, handle, entries) ==
    H.ControlResult{initial, G.remove(instance, handle, entries), H.Metadata{W.InvalidatedReceipt{}}} : H.ControlResult}
def known_fitting_invalidation_returns_receipt_and_removes_handle(c, initial, instance, handle, entry, entries, present, fits):
  %Equal.sym(Maybe<&2, G.Entry>, G.lookup(instance, handle, entries), Some{entry}, present) :
    {H.invalidate_found(_, c, initial, instance, handle, entries) ==
      H.ControlResult{initial, G.remove(instance, handle, entries), H.Metadata{W.InvalidatedReceipt{}}} : H.ControlResult}
  %Equal.sym(Bool, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), True{}, fits) :
    {H.invalidate_fits(_, initial, instance, handle, entries) ==
      H.ControlResult{initial, G.remove(instance, handle, entries), H.Metadata{W.InvalidatedReceipt{}}} : H.ControlResult}
  {==}

law cleanup_cannot_restore_registry:
  for failed: Bool
  for +result: H.ControlResult
  {H.registry(H.cleanup_invalidation(failed, result)) == H.registry(result) : List<&2, G.Entry>}
def cleanup_cannot_restore_registry(failed, result):
  match failed result:
    case False{} result: {==}
    case True{} H.ControlResult{state, entries, H.Error{status}}: {==}
    case True{} H.ControlResult{state, entries, H.Metadata{W.PreparedReceipt{handle}}}: {==}
    case True{} H.ControlResult{state, entries, H.Metadata{W.InvalidatedReceipt{}}}: {==}

law cleanup_preserves_published_state:
  for failed: Bool
  for +result: H.ControlResult
  {H.state(H.cleanup_invalidation(failed, result)) == H.state(result) : D.State}
def cleanup_preserves_published_state(failed, result):
  match failed result:
    case False{} result: {==}
    case True{} H.ControlResult{state, entries, H.Error{status}}: {==}
    case True{} H.ControlResult{state, entries, H.Metadata{W.PreparedReceipt{handle}}}: {==}
    case True{} H.ControlResult{state, entries, H.Metadata{W.InvalidatedReceipt{}}}: {==}
