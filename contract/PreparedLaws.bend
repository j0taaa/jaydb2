# Authorized prepared-protocol extension (2026-11-06). This is an additive
# contract for physical prepared calls, NOT a weakening of LAWS.Contract or a
# claim that the old ordinary-wire theorem covers the extended executable.
# Control metadata never becomes a transaction response or published state.
import Base
import ./Data.bend as D
import ./Interface.bend as I
import ./Logic.bend as L
import ./Protocol.bend as P
import ./PreparedProtocol.bend as W
import ./PreparedRegistry.bend as G
import ./Requirements.bend as R
import ./Resources.bend as X
import ./Semantics.bend as S
import ./ReadOnlyContract.bend as RO

# This relation is fixed by the concrete compiler/host environment, with the
# same completeness obligation as Interface.Environment. It means CURRENT
# exact dependencies, original literals, native executable and program binding;
# neither a stored hash nor the registry's seal String supplies its proof.
type Artifacts is Type:
  Artifacts{intact: String -> String -> S.Configuration -> G.Entry -> S.Program -> I.Scenario -> Nat -> Type,
    cleanup_failed: String -> String -> G.Entry -> I.Scenario -> Nat -> String -> Bool -> Type}

def Intact(artifacts: Artifacts, native: String, instance: String,
  c: S.Configuration, entry: G.Entry, program: S.Program, scenario: I.Scenario, time: Nat) -> Type:
  Artifacts{relation, cleanup} = artifacts
  relation(native, instance, c, entry, program, scenario, time)

def CleanupOfSelected(artifacts: Artifacts, native: String, instance: String,
  entry: G.Entry, scenario: I.Scenario, time: Nat, identifier: String, fatal: Bool) -> Type:
  Artifacts{intact, relation} = artifacts
  relation(native, instance, entry, scenario, time, identifier, fatal)

# The original proof text derives this universal target, not a fabricated
# concrete derivation with that same text. Instantiation is a separate proof.
def Universal(-c: S.Configuration, -source: String, -program: S.Program) -> Type:
  @context: D.Context -> @arguments: D.Value ->
    R.Certifies(c, source, program, context, arguments)

def CertificateValid(-a: I.Environment, -c: S.Configuration,
  -entry: G.Entry, -program: S.Program) -> Type:
  L.E<I.Bound(a, c, G.code(entry), program),
    L.E<I.Derives(a, c, G.proof(entry), Universal(c, G.code(entry), program)),
      Universal(c, G.code(entry), program)>>

# Read-only capability additionally needs the exact existing whole-program
# target. A caller-supplied proposition or a mode bit cannot replace it.
def ReadCertificateValid(-a: I.Environment, -c: S.Configuration,
  -entry: G.Entry, -program: S.Program) -> Type:
  L.E<CertificateValid(a, c, entry, program),
    L.E<I.Derives(a, c, G.proof(entry), RO.Program(program)), RO.Program(program)>>

# This logical request is NOT re-encoded and compared with physical input.
def resolved(raw: P.Request, +entry: G.Entry) -> P.Request:
  P.Request{credential, handle, arguments, unused} = raw
  P.Request{credential, G.code(entry), arguments, G.proof(entry)}

def Authenticated(-state: D.State, -raw: P.Request, -context: D.Context) -> Type:
  {D.authenticate(state, I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}

def HandleFields(-raw: P.Request, -entry: G.Entry) -> Type:
  L.E<{I.code(raw) == G.handle(entry) : String}, {I.proof(raw) == "" : String}>

def ModeCertificateCases(mode: Bool, -a: I.Environment, -c: S.Configuration,
  -entry: G.Entry, -program: S.Program) -> Type:
  match mode:
    case False{}: CertificateValid(a, c, entry, program)
    case True{}: ReadCertificateValid(a, c, entry, program)

def ModeCertificateValid(-a: I.Environment, -c: S.Configuration,
  +entry: G.Entry, -program: S.Program) -> Type:
  ModeCertificateCases(G.read_only(entry), a, c, entry, program)

# Semantic resolution must follow fresh authentication. A scheduler may make
# an unauthorizing registry read to classify a read batch; that is not Ready.
def Ready(-a: I.Environment, -artifacts: Artifacts, -native: String,
  -world: Nat, -time: Nat, -c: S.Configuration, -state: D.State,
  -input: X.Reception, -instance: String, -entries: List<&2, G.Entry>,
  -raw: P.Request, entry: G.Entry, -context: D.Context, -program: S.Program) -> Type:
  L.E<W.Received(c, input, W.Extension{W.Execute{}, raw}),
    L.E<Authenticated(state, raw, context),
      L.E<HandleFields(raw, entry),
        L.E<{G.lookup(instance, I.code(raw), entries) == Some{entry} : Maybe<&2, G.Entry>},
          L.E<ModeCertificateValid(a, c, entry, program),
            Intact(artifacts, native, instance, c, entry, program,
              I.Serve{world, c, state, input}, time)>>>>>

def PreparationMode(operation: W.Operation, -a: I.Environment,
  -c: S.Configuration, -entry: G.Entry, -program: S.Program) -> Type:
  match operation:
    case W.Prepare{}:
      L.E<{G.read_only(entry) == False{} : Bool}, CertificateValid(a, c, entry, program)>
    case W.PrepareRead{}:
      L.E<{G.read_only(entry) == True{} : Bool}, ReadCertificateValid(a, c, entry, program)>
    case _: Empty

# Admission retains exact original source and proof. An authenticated actor
# does not become the owner of the handle; every later execution authenticates
# its own current credential. No preparation context/arguments are captured.
def PreparationAuthorized(-a: I.Environment, -c: S.Configuration,
  -state: D.State, -input: X.Reception, -instance: String,
  operation: W.Operation, -raw: P.Request, -entry: G.Entry, -context: D.Context,
  -program: S.Program) -> Type:
  L.E<W.Received(c, input, W.Extension{operation, raw}),
    L.E<Authenticated(state, raw, context),
      L.E<{G.instance(entry) == instance : String},
        L.E<{G.code(entry) == I.code(raw) : String},
          L.E<{G.proof(entry) == I.proof(raw) : String},
            PreparationMode(operation, a, c, entry, program)>>>>>

# Registry and published database state are different objects. Receipt errors
# never become data publication. A successful receipt is prepared BEFORE its
# associated registry change; delivery may fail afterwards without rollback.
type ControlResponse is Data:
  Metadata{receipt: W.Receipt}
  Error{status: S.Status}

def response_value(response: ControlResponse) -> D.Value:
  match response:
    case Metadata{receipt}: W.receipt_value(receipt)
    case Error{status}: S.response_value(S.response_error(status))

type ControlResult is Data:
  ControlResult{state: D.State, entries: List<&2, G.Entry>, response: ControlResponse}

def state(result: ControlResult) -> D.State:
  ControlResult{s, entries, response} = result
  s

def registry(result: ControlResult) -> List<&2, G.Entry>:
  ControlResult{s, entries, response} = result
  entries

def response(result: ControlResult) -> ControlResponse:
  ControlResult{s, entries, response} = result
  response

def register_fits(fits: Bool, state: D.State, +entry: G.Entry,
  entries: List<&2, G.Entry>) -> ControlResult:
  match fits:
    case False{}: ControlResult{state, entries, Error{S.Limit{}}}
    case True{}: ControlResult{state, Con{entry, entries}, Metadata{W.PreparedReceipt{G.handle(entry)}}}

def register_found(found: Maybe<&2, G.Entry>, c: S.Configuration,
  state: D.State, +entry: G.Entry, entries: List<&2, G.Entry>) -> ControlResult:
  match found:
    case Some{previous}: ControlResult{state, entries, Error{S.Failure{}}}
    case None{}:
      register_fits(R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})), state, entry, entries)

# Pure result computation after candidate selection. This function does not
# implement or prove authentication/admission; ControlOutcome separately binds
# actual successful effects to RegistrationReady and the exact admitted seal.
def register(c: S.Configuration, state: D.State, instance: String,
  +entry: G.Entry, +entries: List<&2, G.Entry>) -> ControlResult:
  register_found(G.lookup(instance, G.handle(entry), entries), c, state, entry, entries)

def invalidate_fits(fits: Bool, state: D.State, instance: String,
  handle: String, +entries: List<&2, G.Entry>) -> ControlResult:
  match fits:
    case False{}: ControlResult{state, entries, Error{S.Limit{}}}
    case True{}: ControlResult{state, G.remove(instance, handle, entries), Metadata{W.InvalidatedReceipt{}}}

def invalidate_found(found: Maybe<&2, G.Entry>, c: S.Configuration,
  state: D.State, instance: String, handle: String,
  entries: List<&2, G.Entry>) -> ControlResult:
  match found:
    case None{}: ControlResult{state, entries, Error{S.Failure{}}}
    case Some{entry}:
      invalidate_fits(R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), state, instance, handle, entries)

# Pure invalidation-result computation. Current authentication and exact
# physical reception belong to ControlOutcome, not to this helper alone.
# Unknown handles have a specific protocol failure cause.
def invalidate(c: S.Configuration, state: D.State, +instance: String,
  +handle: String, +entries: List<&2, G.Entry>) -> ControlResult:
  invalidate_found(G.lookup(instance, handle, entries), c, state, instance, handle, entries)

# Actual host order: registry removal precedes directory cleanup. A cleanup
# failure can replace the receipt by failure WITHOUT restoring registration.
def cleanup_invalidation(failed: Bool, result: ControlResult) -> ControlResult:
  match failed result:
    case False{} result: result
    case True{} ControlResult{state, entries, Metadata{W.InvalidatedReceipt{}}}:
      ControlResult{state, entries, Error{S.Failure{}}}
    case True{} result: result

# Receipt bounds are a separate limit cause; ordinary input, state and final
# response limits keep their original meanings. This does not admit a valid
# transaction's arbitrary refusal or an invented technical failure.
def ReceiptTooLarge(-c: S.Configuration, -receipt: W.Receipt) -> Type:
  {R.fits(R.limit_response(S.limits(c)), W.receipt_value(receipt)) == False{} : Bool}

# Exact bytes and actual interruption remain obligatory after metadata change.
def Delivery(-receipt: W.Receipt, -bytes: List<&2, U32>, -sent: List<&2, U32>,
  -a: I.Environment, -native: String, -scenario: I.Scenario, -time: Nat) -> Type:
  L.E<W.ReceiptEncoding(receipt, bytes),
    L.Disjunction<{sent == bytes : List<&2, U32>},
      L.E<L.Prefix(U32, sent, bytes), I.FailureDeliveryReal(a, native, scenario, time)>>>

law universal_certificate_specializes:
  for -c: S.Configuration
  for -source: String
  for -program: S.Program
  for context: D.Context
  for arguments: D.Value
  for certificate: Universal(c, source, program)
  R.Certifies(c, source, program, context, arguments)
def universal_certificate_specializes(c, source, program, context, arguments, certificate):
  certificate(context, arguments)

law register_fit_stage_preserves_published_state:
  for fits: Bool
  for +initial: D.State
  for entry: G.Entry
  for entries: List<&2, G.Entry>
  {state(register_fits(fits, initial, entry, entries)) == initial : D.State}
def register_fit_stage_preserves_published_state(fits, initial, entry, entries):
  match fits:
    case False{}: {==}
    case True{}: {==}

law invalidate_fit_stage_preserves_published_state:
  for fits: Bool
  for +initial: D.State
  for instance: String
  for handle: String
  for entries: List<&2, G.Entry>
  {state(invalidate_fits(fits, initial, instance, handle, entries)) == initial : D.State}
def invalidate_fit_stage_preserves_published_state(fits, initial, instance, handle, entries):
  match fits:
    case False{}: {==}
    case True{}: {==}

law oversized_registration_receipt_cannot_change_registry:
  for initial: D.State
  for entry: G.Entry
  for +entries: List<&2, G.Entry>
  {registry(register_fits(False{}, initial, entry, entries)) == entries : List<&2, G.Entry>}
def oversized_registration_receipt_cannot_change_registry(initial, entry, entries):
  {==}

law oversized_invalidation_receipt_cannot_change_registry:
  for initial: D.State
  for instance: String
  for handle: String
  for +entries: List<&2, G.Entry>
  {registry(invalidate_fits(False{}, initial, instance, handle, entries)) == entries : List<&2, G.Entry>}
def oversized_invalidation_receipt_cannot_change_registry(initial, instance, handle, entries):
  {==}

law failed_cleanup_keeps_actual_removed_registry:
  for initial: D.State
  for +entries: List<&2, G.Entry>
  {cleanup_invalidation(True{}, ControlResult{initial, entries, Metadata{W.InvalidatedReceipt{}}}) ==
    ControlResult{initial, entries, Error{S.Failure{}}} : ControlResult}
def failed_cleanup_keeps_actual_removed_registry(initial, entries):
  {==}

# Generated handles have the actual 256-bit lower-case hexadecimal shape.
def hex_digit(+code: U32) -> Bool:
  (U32.is_ge(code, 48) && U32.is_le(code, 57)) ||
    (U32.is_ge(code, 97) && U32.is_le(code, 102))

def hex_text(text: String) -> Bool:
  match text:
    case SNil{}: True{}
    case SCon{Chr{code}, rest}: hex_digit(code) && hex_text(rest)

def HandleValid(+handle: String) -> Type:
  L.E<{String.length(handle) == 64n : Nat}, {hex_text(handle) == True{} : Bool}>

def HandleOperation(operation: W.Operation) -> Type:
  match operation:
    case W.Execute{}: Unit
    case W.Invalidate{}: Unit
    case _: Empty

# Registration is authorized only by a universal derivation of the exact
# source, current authentication, a current sealed artifact, and a fresh handle.
def RegistrationReady(-a: I.Environment, -artifacts: Artifacts, -native: String,
  -world: Nat, -time: Nat, -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -entries: List<&2, G.Entry>, operation: W.Operation,
  -raw: P.Request, -entry: G.Entry, -context: D.Context, -program: S.Program) -> Type:
  L.E<PreparationAuthorized(a, c, initial, input, instance, operation, raw, entry, context, program),
    L.E<Intact(artifacts, native, instance, c, entry, program,
      I.Serve{world, c, initial, input}, time),
      L.E<HandleValid(G.handle(entry)),
        {G.lookup(instance, G.handle(entry), entries) == None{} : Maybe<&2, G.Entry>}>>>

def InvalidationReady(-c: S.Configuration, -initial: D.State,
  -input: X.Reception, -instance: String, -entries: List<&2, G.Entry>,
  -raw: P.Request, -entry: G.Entry, -context: D.Context) -> Type:
  L.E<W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
    L.E<Authenticated(initial, raw, context),
      L.E<HandleFields(raw, entry),
        {G.lookup(instance, I.code(raw), entries) == Some{entry} : Maybe<&2, G.Entry>}>>>

# Public success obligations bind ACTUAL results, not just calls to a helper.
def MetadataCorrect(receipt: W.Receipt, -a: I.Environment, -artifacts: Artifacts,
  -native: String, -world: Nat, -time: Nat, -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -after: List<&2, G.Entry>,
  operation: W.Operation, -raw: P.Request) -> Type:
  match receipt:
    case W.PreparedReceipt{handle}:
      &entry: G.Entry -> &context: D.Context -> &program: S.Program ->
        L.E<RegistrationReady(a, artifacts, native, world, time, c, initial, input, instance, before, operation, raw, entry, context, program),
          L.E<{G.handle(entry) == handle : String}, {after == Con{entry, before} : List<&2, G.Entry>}>>
    case W.InvalidatedReceipt{}:
      &entry: G.Entry -> &context: D.Context ->
        L.E<{operation == W.Invalidate{} : W.Operation},
          L.E<InvalidationReady(c, initial, input, instance, before, raw, entry, context),
            {after == G.remove(instance, I.code(raw), before) : List<&2, G.Entry>}>>

# A universal certificate can be absent even when some concrete call proof
# exists. Read preparation additionally requires the fixed whole-program proof.
def AdmissionDerivation(operation: W.Operation, -a: I.Environment,
  -c: S.Configuration, -raw: P.Request, -program: S.Program) -> Type:
  match operation:
    case W.Prepare{}:
      L.E<I.Bound(a, c, I.code(raw), program),
        I.Derives(a, c, I.proof(raw), Universal(c, I.code(raw), program))>
    case W.PrepareRead{}:
      L.E<I.Bound(a, c, I.code(raw), program),
        L.E<I.Derives(a, c, I.proof(raw), Universal(c, I.code(raw), program)),
          I.Derives(a, c, I.proof(raw), RO.Program(program))>>
    case _: Empty

def PreparationOperation(operation: W.Operation) -> Type:
  match operation:
    case W.Prepare{}: Unit
    case W.PrepareRead{}: Unit
    case _: Empty

def WithoutAdmission(-operation: W.Operation, -a: I.Environment,
  -c: S.Configuration, -raw: P.Request) -> Type:
  @program: S.Program -> AdmissionDerivation(operation, a, c, raw, program) -> Empty

# Genuine failures precede the response and belong to the same physical call.
def RealFailureBefore(-a: I.Environment, -native: String, -world: Nat,
  -c: S.Configuration, -initial: D.State, -input: X.Reception, -time: Nat) -> Type:
  &at: Nat -> &stage: X.Stage -> &identifier: String -> &fatal: Bool ->
    L.E<{Nat.is_lt(at, time) == True{} : Bool},
      L.E<I.Happens(a, native, I.Serve{world, c, initial, input}, at, I.FailedEnvironment{stage, identifier, fatal}),
        I.FailureReal(a, native, I.Serve{world, c, initial, input}, at, stage, identifier, fatal)>>

# Only actual invalidation cleanup may fail after a control registry mutation.
# Stage Prepare denotes the host's cleanup of that selected directory; its
# exact physical origin remains part of the complete failure correspondence.
def CleanupFailure(-a: I.Environment, -artifacts: Artifacts, -native: String,
  -instance: String, -entry: G.Entry, -world: Nat, -c: S.Configuration,
  -initial: D.State, -input: X.Reception, -time: Nat) -> Type:
  &at: Nat -> &identifier: String -> &fatal: Bool ->
    L.E<{Nat.is_lt(at, time) == True{} : Bool},
      L.E<I.Happens(a, native, I.Serve{world, c, initial, input}, at, I.FailedEnvironment{X.Prepare{}, identifier, fatal}),
        L.E<I.FailureReal(a, native, I.Serve{world, c, initial, input}, at, X.Prepare{}, identifier, fatal),
          CleanupOfSelected(artifacts, native, instance, entry,
            I.Serve{world, c, initial, input}, at, identifier, fatal)>>>

# Overflow is checked before sealing. A rejected oversized receipt need not
# leave an intact artifact behind; it must still follow genuine admission.
def RegistrationCandidate(-a: I.Environment, -c: S.Configuration,
  -initial: D.State, -input: X.Reception, -instance: String,
  -before: List<&2, G.Entry>, operation: W.Operation, -raw: P.Request,
  -entry: G.Entry, -context: D.Context, -program: S.Program) -> Type:
  L.E<PreparationAuthorized(a, c, initial, input, instance, operation, raw, entry, context, program),
    L.E<HandleValid(G.handle(entry)),
      {G.lookup(instance, G.handle(entry), before) == None{} : Maybe<&2, G.Entry>}>>

def OversizedControlReceipt(-a: I.Environment, -artifacts: Artifacts, -native: String,
  -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, operation: W.Operation, -raw: P.Request) -> Type:
  L.Disjunction<
    &entry: G.Entry -> &context: D.Context -> &program: S.Program ->
      L.E<RegistrationCandidate(a, c, initial, input, instance, before, operation, raw, entry, context, program),
        ReceiptTooLarge(c, W.PreparedReceipt{G.handle(entry)})>,
    &entry: G.Entry -> &context: D.Context ->
      L.E<{operation == W.Invalidate{} : W.Operation},
        L.E<InvalidationReady(c, initial, input, instance, before, raw, entry, context), ReceiptTooLarge(c, W.InvalidatedReceipt{})>>>

# Known protocol errors for a valid decoded extension. This does not pretend
# arbitrary malformed receptions have a valid WireRequest witness.
def ProtocolError(status: S.Status, operation: W.Operation, -a: I.Environment,
  -artifacts: Artifacts, -native: String, -world: Nat, -c: S.Configuration,
  -initial: D.State, -input: X.Reception, -time: Nat, -instance: String,
  -before: List<&2, G.Entry>, -after: List<&2, G.Entry>, -raw: P.Request) -> Type:
  match status:
    case S.Authentication{}:
      L.E<{D.authenticate(initial, I.credential(raw)) == None{} : Maybe<&2, D.Context>},
        {after == before : List<&2, G.Entry>}>
    case S.Input{}:
      &context: D.Context ->
        L.E<HandleOperation(operation), L.E<Authenticated(initial, raw, context),
          L.E<{String.eq(I.proof(raw), "") == False{} : Bool}, {after == before : List<&2, G.Entry>}>>>
    case S.Certificate{}:
      &context: D.Context ->
        L.E<PreparationOperation(operation), L.E<Authenticated(initial, raw, context),
          L.E<WithoutAdmission(operation, a, c, raw), {after == before : List<&2, G.Entry>}>>>
    case S.Limit{}:
      L.E<OversizedControlReceipt(a, artifacts, native, c, initial, input, instance, before, operation, raw),
        {after == before : List<&2, G.Entry>}>
    case S.Failure{}:
      L.Disjunction<
        &context: D.Context ->
          L.E<HandleOperation(operation), L.E<Authenticated(initial, raw, context),
            L.E<{I.proof(raw) == "" : String},
              L.E<{G.lookup(instance, I.code(raw), before) == None{} : Maybe<&2, G.Entry>}, {after == before : List<&2, G.Entry>}>>>>,
        L.Disjunction<L.E<RealFailureBefore(a, native, world, c, initial, input, time), {after == before : List<&2, G.Entry>}>,
          &entry: G.Entry -> &context: D.Context ->
            L.E<{operation == W.Invalidate{} : W.Operation},
              L.E<InvalidationReady(c, initial, input, instance, before, raw, entry, context),
                L.E<{R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
                  L.E<CleanupFailure(a, artifacts, native, instance, entry, world, c, initial, input, time),
                    {after == G.remove(instance, I.code(raw), before) : List<&2, G.Entry>}>>>>>>
    case _: Empty

# The actual metadata result must preserve the entire published pair, use a
# canonical bounded frame, and have exactly one authorized effect/cause.
def OutcomeCause(result: ControlResponse, -a: I.Environment, -artifacts: Artifacts,
  -native: String, -world: Nat, -c: S.Configuration, -initial: D.State,
  -input: X.Reception, -time: Nat, -instance: String, -before: List<&2, G.Entry>,
  -after: List<&2, G.Entry>, operation: W.Operation, -raw: P.Request) -> Type:
  match result:
    case Metadata{receipt}:
      MetadataCorrect(receipt, a, artifacts, native, world, time, c, initial, input, instance, before, after, operation, raw)
    case Error{status}:
      ProtocolError(status, operation, a, artifacts, native, world, c, initial, input, time, instance, before, after, raw)

def ControlOutcome(-a: I.Environment, -artifacts: Artifacts, -native: String,
  -world: Nat, -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -time: Nat, -instance: String, -before: List<&2, G.Entry>, operation: W.Operation,
  -raw: P.Request, +result: ControlResult, -previous_response: List<&2, U32>,
  -next_response: List<&2, U32>, -bytes: List<&2, U32>) -> Type:
  L.E<W.Received(c, input, W.Extension{operation, raw}),
    L.E<{state(result) == initial : D.State},
      L.E<{next_response == previous_response : List<&2, U32>},
        L.E<P.Message(response_value(response(result)), bytes),
          L.E<{R.fits(R.limit_response(S.limits(c)), response_value(response(result))) == True{} : Bool},
            OutcomeCause(response(result), a, artifacts, native, world, c, initial, input,
              time, instance, before, registry(result), operation, raw)>>>>>

# A technical failure before decoding is meaningful on arbitrary receptions;
# it preserves database/registry state and cannot fabricate a decoded request.
def UndecodedFailure(-a: I.Environment, -native: String, -world: Nat,
  -c: S.Configuration, -initial: D.State, -input: X.Reception, -time: Nat,
  -before: List<&2, G.Entry>, -result: ControlResult) -> Type:
  L.E<RealFailureBefore(a, native, world, c, initial, input, time),
    {result == ControlResult{initial, before, Error{S.Failure{}}} : ControlResult}>

# A complete malformed extension body has no exact typed wire interpretation.
# This rejects unknown/truncated opcodes as well as malformed inner records.
def InvalidWire(-c: S.Configuration, -input: X.Reception) -> Type:
  L.E<X.ReceptionValid(input),
    &bytes: List<&2, U32> ->
      L.E<{X.decide_reception(c, input) == X.ProcessBody{bytes} : X.Disposition},
        @wire: W.WireRequest -> W.BodyEncoding(wire, bytes) -> Empty>>

# Actual control observations are supplied by the FIXED technical environment,
# not emitted selectively by the candidate. Every metadata result and every
# registry mutation must appear, including errors/lost delivery. These are
# specification events, not a new public log or user-selected policy.
type ControlObservation is Data:
  DecodedControl{world: Nat, initial: D.State, input: X.Reception, time: Nat,
    instance: String, before: List<&2, G.Entry>, operation: W.Operation,
    raw: P.Request, result: ControlResult, previous_response: List<&2, U32>,
    next_response: List<&2, U32>, bytes: List<&2, U32>}
  FailedBeforeDecode{world: Nat, initial: D.State, input: X.Reception,
    time: Nat, before: List<&2, G.Entry>, result: ControlResult,
    previous_response: List<&2, U32>, next_response: List<&2, U32>, bytes: List<&2, U32>}
  MalformedWire{initial: D.State, input: X.Reception, before: List<&2, G.Entry>,
    result: ControlResult, previous_response: List<&2, U32>,
    next_response: List<&2, U32>, bytes: List<&2, U32>}

def FixedErrorOutcome(-status: S.Status, -c: S.Configuration, -initial: D.State,
  -before: List<&2, G.Entry>, -result: ControlResult, -previous: List<&2, U32>,
  -next: List<&2, U32>, -bytes: List<&2, U32>) -> Type:
  L.E<{result == ControlResult{initial, before, Error{status}} : ControlResult},
    L.E<{next == previous : List<&2, U32>},
      L.E<P.Message(S.response_value(S.response_error(status)), bytes),
        {R.fits(R.limit_response(S.limits(c)), S.response_value(S.response_error(status))) == True{} : Bool}>>>

def ObservationCorrect(observation: ControlObservation, -a: I.Environment,
  -artifacts: Artifacts, -native: String, -c: S.Configuration) -> Type:
  match observation:
    case DecodedControl{world, initial, input, time, instance, before, operation,
      raw, result, previous, next, bytes}:
      ControlOutcome(a, artifacts, native, world, c, initial, input, time,
        instance, before, operation, raw, result, previous, next, bytes)
    case FailedBeforeDecode{world, initial, input, time, before, result, previous, next, bytes}:
      L.E<RealFailureBefore(a, native, world, c, initial, input, time),
        FixedErrorOutcome(S.Failure{}, c, initial, before, result, previous, next, bytes)>
    case MalformedWire{initial, input, before, result, previous, next, bytes}:
      L.E<InvalidWire(c, input),
        FixedErrorOutcome(S.Input{}, c, initial, before, result, previous, next, bytes)>

# This is the additional physical-control obligation, NOT a replacement for
# the eight transaction laws, progress, or the complete native refinement.
# A concrete model still has to establish this type for all actual observations.
def ControlLaw(-a: I.Environment, -artifacts: Artifacts, -native: String,
  -c: S.Configuration, -observes: String -> ControlObservation -> Type) -> Type:
  @observation: ControlObservation -> observes(native, observation) ->
    ObservationCorrect(observation, a, artifacts, native, c)
