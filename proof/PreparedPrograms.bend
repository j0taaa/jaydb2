# Prepared execution specializes a checked universal certificate to the actual
# authenticated call. Registry lookup and physical framing remain host contracts;
# a handle is never identified with the original program's source text.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ../src/Input.bend as E
import ../src/Prepared.bend as Prepared
import ./Call.bend as Call

def Universal(-c: S.Configuration, -code: String, -program: S.Program) -> Type:
  @context: D.Context -> @arguments: D.Value ->
    R.Certifies(c, code, program, context, arguments)

law resolution_binds_original_source_and_preserves_call:
  for raw: P.Request
  for code: String
  for proof: String
  L.E<{I.code(Prepared.resolve_request(raw, code, proof)) == code : String},
    L.E<{I.proof(Prepared.resolve_request(raw, code, proof)) == proof : String},
      L.E<{I.credential(Prepared.resolve_request(raw, code, proof)) == I.credential(raw) : String},
        {I.arguments(Prepared.resolve_request(raw, code, proof)) == I.arguments(raw) : D.Value}>>>
def resolution_binds_original_source_and_preserves_call(raw, code, proof):
  match raw:
    case P.Request{credential, handle, arguments, unused}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, {==}}}}

law resolution_preserves_current_authentication:
  for -state: D.State
  for raw: P.Request
  for code: String
  for proof: String
  {D.authenticate(state, I.credential(Prepared.resolve_request(raw, code, proof))) ==
    D.authenticate(state, I.credential(raw)) : Maybe<&2, D.Context>}
def resolution_preserves_current_authentication(state, raw, code, proof):
  match raw:
    case P.Request{credential, handle, arguments, unused}: {==}

law authenticated_resolution_preserves_state_and_context:
  for -state: D.State
  for -raw: P.Request
  for -context: D.Context
  for -code: String
  for -proof: String
  {Prepared.resolve_analysis(E.Received{state, raw, context}, code, proof) ==
    E.Received{state, Prepared.resolve_request(raw, code, proof), context} : E.Analysis}
def authenticated_resolution_preserves_state_and_context(state, raw, context, code, proof):
  {==}

law specialize_for_actual_arguments:
  for -c: S.Configuration
  for -code: String
  for -program: S.Program
  for context: D.Context
  for raw: P.Request
  for proof: String
  for certificate: Universal(c, code, program)
  R.Certifies(c, I.code(Prepared.resolve_request(raw, code, proof)), program,
    context, I.arguments(Prepared.resolve_request(raw, code, proof)))
def specialize_for_actual_arguments(c, code, program, context, raw, proof, certificate):
  match raw:
    case P.Request{credential, handle, arguments, unused}:
      certificate(context, arguments)

# Uses the current valid state and the actual Core execution result. Neither
# final-state validity nor permission to publish is supplied as a premise.
law prepared_call_prepares_and_concludes:
  for c: S.Configuration
  for -code: String
  for program: S.Program
  for +context: D.Context
  for raw: P.Request
  for certificate: Universal(c, code, program)
  for +state: D.State
  for valid: R.Valid(c, state)
  for authentication: {D.authenticate(state, I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for +n: Nat
  for +working: D.State
  for +events: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for execution: {N.traverse(n, N.start(program, context, I.arguments(raw), state), S.schema(c)) ==
    S.Final{working, events, proposal} : S.Trace}
  for configuration_valid: {R.configuration_is_valid(c) == True{} : Bool}
  Call.ConclusionIntegral(c, state, working, events, proposal)
def prepared_call_prepares_and_concludes(c, code, program, context, raw, certificate,
  state, valid, authentication, n, working, events, proposal, execution, configuration_valid):
  match raw:
    case P.Request{credential, handle, +arguments, unused}:
      Call.call_authenticated_prepares_and_concludes(c, code, program, context, arguments,
        certificate(context, arguments), state, valid, credential, authentication,
        n, working, events, proposal, execution, configuration_valid)
