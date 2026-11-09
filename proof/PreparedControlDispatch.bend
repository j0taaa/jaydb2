# Complete preparation decision over the actual current authentication result,
# primitive admission verdict, receipt bound and artifact sealing result.
# This is a pure controller model. It does not assert that Rust implements it.
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
import ./Preparation.bend as Preparation
import ./Call.bend as Call

# Primitive tool results are not certificates. ToolEvidence below must justify
# the exact source judgment or a real technical failure for this physical call.
type Gate is Data:
  Refuted{}
  Broken{}
  Candidate{entry: G.Entry, sealed: Bool}

def sealed_result(sealed: Bool, initial: D.State, +entry: G.Entry,
  before: List<&2, G.Entry>) -> H.ControlResult:
  match sealed:
    case False{}: H.ControlResult{initial, before, H.Error{S.Failure{}}}
    case True{}: H.ControlResult{initial, Con{entry, before}, H.Metadata{W.PreparedReceipt{G.handle(entry)}}}

def fitting_result(fits: Bool, sealed: Bool, initial: D.State,
  entry: G.Entry, before: List<&2, G.Entry>) -> H.ControlResult:
  match fits:
    case False{}: H.ControlResult{initial, before, H.Error{S.Limit{}}}
    case True{}: sealed_result(sealed, initial, entry, before)

def gate_result(gate: Gate, c: S.Configuration, initial: D.State,
  before: List<&2, G.Entry>) -> H.ControlResult:
  match gate:
    case Refuted{}: H.ControlResult{initial, before, H.Error{S.Certificate{}}}
    case Broken{}: H.ControlResult{initial, before, H.Error{S.Failure{}}}
    case Candidate{+entry, sealed}:
      fitting_result(R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.PreparedReceipt{G.handle(entry)})), sealed, initial, entry, before)

def authenticated_result(authentication: Maybe<&2, D.Context>, gate: Gate,
  c: S.Configuration, initial: D.State, before: List<&2, G.Entry>) -> H.ControlResult:
  match authentication:
    case None{}: H.ControlResult{initial, before, H.Error{S.Authentication{}}}
    case Some{context}: gate_result(gate, c, initial, before)

def prepare(c: S.Configuration, +initial: D.State, raw: P.Request,
  before: List<&2, G.Entry>, gate: Gate) -> H.ControlResult:
  authenticated_result(D.authenticate(initial, I.credential(raw)), gate, c, initial, before)

# The selected current artifact contract is needed only AFTER a fitting
# receipt. An oversized receipt does not falsely claim that sealing succeeded.
def SealEvidence(fits: Bool, sealed: Bool, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, -c: S.Configuration, -initial: D.State,
  -input: X.Reception, -instance: String, -entry: G.Entry, -program: S.Program) -> Type:
  match fits sealed:
    case False{} _: Unit
    case True{} False{}: H.RealFailureBefore(a, native, world, c, initial, input, time)
    case True{} True{}:
      L.E<H.Intact(artifacts, native, instance, c, entry, program,
        I.Serve{world, c, initial, input}, time), Unit>

# Admission facts expose the actual universal/read derivations, exact original
# literals and fresh generated handle. No outcome/cause/state conclusion occurs.
def CandidateEvidence(-operation: W.Operation, -a: I.Environment,
  -c: S.Configuration, -instance: String, -before: List<&2, G.Entry>,
  -raw: P.Request, -entry: G.Entry, -program: S.Program) -> Type:
  L.E<{G.instance(entry) == instance : String},
    L.E<{G.code(entry) == I.code(raw) : String},
      L.E<{G.proof(entry) == I.proof(raw) : String},
        L.E<H.PreparationMode(operation, a, c, entry, program),
          L.E<H.HandleValid(G.handle(entry)),
            {G.lookup(instance, G.handle(entry), before) == None{} : Maybe<&2, G.Entry>}>>>>>

def ToolEvidence(gate: Gate, -operation: W.Operation, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -raw: P.Request) -> Type:
  match gate:
    case Refuted{}: H.WithoutAdmission(operation, a, c, raw)
    case Broken{}: H.RealFailureBefore(a, native, world, c, initial, input, time)
    case Candidate{entry, sealed}:
      &program: S.Program ->
        L.E<CandidateEvidence(operation, a, c, instance, before, raw, entry, program),
          SealEvidence(R.fits(R.limit_response(S.limits(c)),
            W.receipt_value(W.PreparedReceipt{G.handle(entry)})), sealed,
            a, artifacts, native, world, time, c, initial, input, instance, entry, program)>

# Authentication failure must not depend on a checker or sealing result.
def ToolsAfterAuthentication(authentication: Maybe<&2, D.Context>, gate: Gate,
  -operation: W.Operation, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, -c: S.Configuration,
  -initial: D.State, -input: X.Reception, -instance: String,
  -before: List<&2, G.Entry>, -raw: P.Request) -> Type:
  match authentication:
    case None{}: Unit
    case Some{context}:
      ToolEvidence(gate, operation, a, artifacts, native, world, time,
        c, initial, input, instance, before, raw)

# One semantic result, from which framing and the full ControlOutcome follow.
def ResultCorrect(-result: H.ControlResult, -operation: W.Operation,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -raw: P.Request) -> Type:
  L.E<{H.state(result) == initial : D.State},
    L.E<{R.fits(R.limit_response(S.limits(c)), H.response_value(H.response(result))) == True{} : Bool},
      H.OutcomeCause(H.response(result), a, artifacts, native, world, c,
        initial, input, time, instance, before, H.registry(result), operation, raw)>>

def fixed_result_correct(~c: S.Configuration, status: S.Status, -operation: W.Operation, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -raw: P.Request,
  valid: {R.configuration_is_valid(c) == True{} : Bool}, error: Preparation.Error(status),
  cause: H.ProtocolError(status, operation, a, artifacts, native, world, c, initial, input, time, instance, before, before, raw)) ->
  ResultCorrect(H.ControlResult{initial, before, H.Error{status}}, operation,
    a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  L.Both{{==}, L.Both{
    Preparation.errors_fixed_fit(status, S.limits(c),
      Preparation.limits_of_configuration(c, valid), error), cause}}

def admitted_candidate(-operation: W.Operation, -a: I.Environment,
  -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -raw: P.Request,
  -entry: G.Entry, -context: D.Context, -program: S.Program,
  received: W.Received(c, input, W.Extension{operation, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  facts: CandidateEvidence(operation, a, c, instance, before, raw, entry, program)) ->
  H.RegistrationCandidate(a, c, initial, input, instance, before, operation,
    raw, entry, context, program):
  L.Both{instance_exact, L.Both{code_exact, L.Both{proof_exact,
    L.Both{mode, L.Both{handle_valid, fresh}}}}} = facts
  L.Both{L.Both{received, L.Both{authenticated, L.Both{instance_exact,
    L.Both{code_exact, L.Both{proof_exact, mode}}}}}, L.Both{handle_valid, fresh}}

def ready_of_candidate(-operation: W.Operation, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -raw: P.Request,
  -entry: G.Entry, -context: D.Context, -program: S.Program,
  candidate: H.RegistrationCandidate(a, c, initial, input, instance, before,
    operation, raw, entry, context, program),
  sealed: H.Intact(artifacts, native, instance, c, entry, program,
    I.Serve{world, c, initial, input}, time)) ->
  H.RegistrationReady(a, artifacts, native, world, time, c, initial, input,
    instance, before, operation, raw, entry, context, program):
  L.Both{authorized, L.Both{handle_valid, fresh}} = candidate
  L.Both{authorized, L.Both{sealed, L.Both{handle_valid, fresh}}}

def admitted_ready(-operation: W.Operation, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  -c: S.Configuration, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -raw: P.Request,
  -entry: G.Entry, -context: D.Context, -program: S.Program,
  received: W.Received(c, input, W.Extension{operation, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  facts: CandidateEvidence(operation, a, c, instance, before, raw, entry, program),
  sealed: H.Intact(artifacts, native, instance, c, entry, program,
    I.Serve{world, c, initial, input}, time)) ->
  H.RegistrationReady(a, artifacts, native, world, time, c, initial, input,
    instance, before, operation, raw, entry, context, program):
  ready_of_candidate(operation, a, artifacts, native, world, time, c, initial,
    input, instance, before, raw, entry, context, program,
    admitted_candidate(operation, a, c, initial, input, instance, before, raw,
      entry, context, program, received, authenticated, facts), sealed)

def candidate_result_correct(~c: S.Configuration, fits: Bool, sealed: Bool, -operation: W.Operation,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat, -initial: D.State,
  -input: X.Reception, -instance: String, -before: List<&2, G.Entry>, -raw: P.Request, +entry: G.Entry,
  context: D.Context, program: S.Program, valid: {R.configuration_is_valid(c) == True{} : Bool},
  receipt_checked: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})) == fits : Bool},
  received: W.Received(c, input, W.Extension{operation, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  facts: CandidateEvidence(operation, a, c, instance, before, raw, entry, program),
  seal: SealEvidence(fits, sealed, a, artifacts, native, world, time, c, initial, input, instance, entry, program)) ->
  ResultCorrect(fitting_result(fits, sealed, initial, entry, before), operation,
    a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  match fits sealed:
    case False{} _:
      fixed_result_correct(c, S.Limit{}, operation, a, artifacts, native, world, time, initial, input,
        instance, before, raw, valid, Unit{},
        L.Both{L.Left{(entry, context, program, L.Both{ admitted_candidate(operation, a, c, initial, input, instance, before, raw, entry, context, program, received, authenticated, facts), receipt_checked})}, {==}})
    case True{} False{}:
      fixed_result_correct(c, S.Failure{}, operation, a, artifacts, native, world, time, initial, input,
        instance, before, raw, valid, Unit{}, L.Right{L.Left{L.Both{seal, {==}}}})
    case True{} True{}:
      L.Both{intact, done} = seal
      L.Both{{==}, L.Both{receipt_checked,
        (entry, context, program, L.Both{
          admitted_ready(operation, a, artifacts, native, world, time, c, initial,
            input, instance, before, raw, entry, context, program,
            received, authenticated, facts, intact), L.Both{{==}, {==}}})}}

def gate_result_correct(~c: S.Configuration, gate: Gate, operation: W.Operation, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat, -initial: D.State, -input: X.Reception,
  -instance: String, -before: List<&2, G.Entry>, -raw: P.Request, context: D.Context,
  preparation: H.PreparationOperation(operation), valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{operation, raw}),
  authenticated: H.Authenticated(initial, raw, context),
  evidence: ToolEvidence(gate, operation, a, artifacts, native, world, time, c, initial, input, instance, before, raw)) ->
  ResultCorrect(gate_result(gate, c, initial, before), operation,
    a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  match gate:
    case Refuted{}:
      fixed_result_correct(c, S.Certificate{}, operation, a, artifacts, native, world, time, initial, input,
        instance, before, raw, valid, Unit{},
        (context, L.Both{preparation, L.Both{authenticated, L.Both{evidence, {==}}}}))
    case Broken{}:
      fixed_result_correct(c, S.Failure{}, operation, a, artifacts, native, world, time, initial, input,
        instance, before, raw, valid, Unit{}, L.Right{L.Left{L.Both{evidence, {==}}}})
    case Candidate{+entry, +sealed}:
      (program, L.Both{facts, seal}) = evidence
      candidate_result_correct(c,
        R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})), sealed,
        operation, a, artifacts, native, world, time, initial, input, instance, before, raw, entry, context,
        program, valid, {==}, received, authenticated, facts, seal)

def authenticated_result_correct(~c: S.Configuration, authentication: Maybe<&2, D.Context>, +gate: Gate,
  operation: W.Operation, -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  -initial: D.State, -input: X.Reception, -instance: String, -before: List<&2, G.Entry>, -raw: P.Request,
  preparation: H.PreparationOperation(operation), valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{operation, raw}),
  authentication_exact: {D.authenticate(initial, I.credential(raw)) == authentication : Maybe<&2, D.Context>},
  evidence: ToolsAfterAuthentication(authentication, gate, operation, a, artifacts, native, world, time, c, initial, input, instance, before, raw)) ->
  ResultCorrect(authenticated_result(authentication, gate, c, initial, before),
    operation, a, artifacts, native, world, time, c, initial, input, instance, before, raw):
  match authentication:
    case None{}:
      fixed_result_correct(c, S.Authentication{}, operation, a, artifacts, native, world, time, initial, input,
        instance, before, raw, valid, Unit{}, L.Both{authentication_exact, {==}})
    case Some{context}:
      gate_result_correct(c, gate, operation, a, artifacts, native, world, time, initial, input, instance,
        before, raw, context, preparation, valid, received, authentication_exact, evidence)

law complete_preparation_result:
  for ~c: S.Configuration
  for operation: W.Operation
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for +initial: D.State
  for -input: X.Reception
  for -instance: String
  for -before: List<&2, G.Entry>
  for +raw: P.Request
  for +gate: Gate
  for preparation: H.PreparationOperation(operation)
  for valid: {R.configuration_is_valid(c) == True{} : Bool}
  for received: W.Received(c, input, W.Extension{operation, raw})
  for evidence: ToolsAfterAuthentication(D.authenticate(initial, I.credential(raw)),
    gate, operation, a, artifacts, native, world, time, c, initial, input, instance, before, raw)
  ResultCorrect(prepare(c, initial, raw, before, gate), operation, a, artifacts,
    native, world, time, c, initial, input, instance, before, raw)
def complete_preparation_result(c, operation, a, artifacts, native, world, time, initial, input, instance,
  before, raw, gate, preparation, valid, received, evidence):
  authenticated_result_correct(c, D.authenticate(initial, I.credential(raw)), gate, operation, a, artifacts,
    native, world, time, initial, input, instance, before, raw, preparation, valid, received, {==}, evidence)

# Physical reception contains only data witnesses/equalities. Duplicate those
# components, never an affine universal certificate or artifact relation.
def copy_received_body(-c: S.Configuration, -input: X.Reception,
  -wire: W.WireRequest, +valid: {X.reception_is_valid(input) == True{} : Bool},
  received: &bytes: List<&2, U32> ->
    L.E<{X.decide_reception(c, input) == X.ProcessBody{bytes} : X.Disposition},
      {W.encode_body(wire) == Some{bytes} : Maybe<&2, List<&2, U32>>}>) -> L.E<W.Received(c, input, wire), W.Received(c, input, wire)>:
  (+bytes, L.Both{+processing, +encoded}) = received
  L.Both{L.Both{valid, (bytes, L.Both{processing, encoded})},
    L.Both{valid, (bytes, L.Both{processing, encoded})}}

law physical_reception_data_can_be_reused:
  for -c: S.Configuration
  for -input: X.Reception
  for -wire: W.WireRequest
  for received: W.Received(c, input, wire)
  L.E<W.Received(c, input, wire), W.Received(c, input, wire)>
def physical_reception_data_can_be_reused(c, input, wire, received):
  L.Both{valid, body} = received
  copy_received_body(c, input, wire, valid, body)

def framed_outcome(-operation: W.Operation, -a: I.Environment,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  -c: S.Configuration, -initial: D.State, -input: X.Reception, -instance: String,
  -before: List<&2, G.Entry>, -raw: P.Request, -result: H.ControlResult,
  -previous: List<&2, U32>,
  received: W.Received(c, input, W.Extension{operation, raw}),
  unchanged: {H.state(result) == initial : D.State},
  bounded: {R.fits(R.limit_response(S.limits(c)), H.response_value(H.response(result))) == True{} : Bool},
  cause: H.OutcomeCause(H.response(result), a, artifacts, native, world, c,
    initial, input, time, instance, before, H.registry(result), operation, raw),
  framed: &bytes: List<&2, U32> -> P.Message(H.response_value(H.response(result)), bytes)) ->
  &bytes: List<&2, U32> -> H.ControlOutcome(a, artifacts, native, world, c, initial,
    input, time, instance, before, operation, raw, result, previous, previous, bytes):
  (bytes, encoding) = framed
  (bytes, L.Both{received, L.Both{unchanged, L.Both{{==},
    L.Both{encoding, L.Both{bounded, cause}}}}})

def correct_result_has_control_outcome(~c: S.Configuration, -operation: W.Operation,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, -initial: D.State, -input: X.Reception, -instance: String,
  -before: List<&2, G.Entry>, -raw: P.Request, +result: H.ControlResult,
  -previous: List<&2, U32>, valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{operation, raw}),
  correct: ResultCorrect(result, operation, a, artifacts, native, world, time,
    c, initial, input, instance, before, raw)) ->
  &bytes: List<&2, U32> -> H.ControlOutcome(a, artifacts, native, world, c, initial,
    input, time, instance, before, operation, raw, result, previous, previous, bytes):
  L.Both{unchanged, L.Both{+bounded, cause}} = correct
  framed_outcome(operation, a, artifacts, native, world, time, c, initial, input,
    instance, before, raw, result, previous, received, unchanged, bounded, cause,
    Call.response_preparable_has_framing(H.response_value(H.response(result)),
      S.limits(c), Preparation.limits_of_configuration(c, valid), bounded))

def preparation_with_received_pair(~c: S.Configuration, operation: W.Operation,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String, -world: Nat,
  -time: Nat, +initial: D.State, -input: X.Reception, -instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request, +gate: Gate, -previous: List<&2, U32>,
  preparation: H.PreparationOperation(operation),
  +valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: L.E<W.Received(c, input, W.Extension{operation, raw}),
    W.Received(c, input, W.Extension{operation, raw})>,
  evidence: ToolsAfterAuthentication(D.authenticate(initial, I.credential(raw)),
    gate, operation, a, artifacts, native, world, time, c, initial, input, instance, before, raw)) ->
  &bytes: List<&2, U32> -> H.ControlOutcome(a, artifacts, native, world, c, initial,
    input, time, instance, before, operation, raw, prepare(c, initial, raw, before, gate),
    previous, previous, bytes):
  L.Both{physical, logical} = received
  correct_result_has_control_outcome(c, operation, a, artifacts, native, world,
    time, initial, input, instance, before, raw, prepare(c, initial, raw, before, gate),
    previous, valid, physical,
    complete_preparation_result(c, operation, a, artifacts, native, world, time, initial, input, instance,
      before, raw, gate, preparation, valid, logical, evidence))

law complete_preparation_control_outcome:
  for ~c: S.Configuration
  for operation: W.Operation
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for +initial: D.State
  for -input: X.Reception
  for -instance: String
  for +before: List<&2, G.Entry>
  for +raw: P.Request
  for +gate: Gate
  for -previous: List<&2, U32>
  for preparation: H.PreparationOperation(operation)
  for valid: {R.configuration_is_valid(c) == True{} : Bool}
  for received: W.Received(c, input, W.Extension{operation, raw})
  for evidence: ToolsAfterAuthentication(D.authenticate(initial, I.credential(raw)),
    gate, operation, a, artifacts, native, world, time, c, initial, input, instance, before, raw)
  exs bytes: List<&2, U32>
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time, instance,
    before, operation, raw, prepare(c, initial, raw, before, gate), previous, previous, bytes)
def complete_preparation_control_outcome(c, operation, a, artifacts, native, world,
  time, initial, input, instance, before, raw, gate, previous, preparation, valid,
  received, evidence):
  preparation_with_received_pair(c, operation, a, artifacts, native, world, time,
    initial, input, instance, before, raw, gate, previous, preparation, valid,
    physical_reception_data_can_be_reused(c, input, W.Extension{operation, raw}, received), evidence)

law receipt_limit_precedes_sealing_failure:
  for initial: D.State
  for entry: G.Entry
  for before: List<&2, G.Entry>
  {fitting_result(False{}, False{}, initial, entry, before) ==
    H.ControlResult{initial, before, H.Error{S.Limit{}}} : H.ControlResult}
def receipt_limit_precedes_sealing_failure(initial, entry, before):
  {==}

law current_authentication_failure_prevents_registration:
  for -c: S.Configuration
  for -initial: D.State
  for -raw: P.Request
  for -before: List<&2, G.Entry>
  for -gate: Gate
  for absent: {D.authenticate(initial, I.credential(raw)) == None{} : Maybe<&2, D.Context>}
  {prepare(c, initial, raw, before, gate) ==
    H.ControlResult{initial, before, H.Error{S.Authentication{}}} : H.ControlResult}
def current_authentication_failure_prevents_registration(c, initial, raw, before, gate, absent):
  %Equal.sym(Maybe<&2, D.Context>, D.authenticate(initial, I.credential(raw)), None{}, absent) :
    {authenticated_result(_, gate, c, initial, before) ==
      H.ControlResult{initial, before, H.Error{S.Authentication{}}} : H.ControlResult}
  {==}
