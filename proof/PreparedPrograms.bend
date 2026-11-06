# Prepared execution specializes a checked universal certificate to the actual
# authenticated call. Registry lookup and physical framing remain host contracts;
# a handle is never identified with the original program's source text.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../contract/Resources.bend as X
import ../src/Core.bend as N
import ../src/Input.bend as E
import ../src/Prepared.bend as Prepared
import ./Call.bend as Call
import ./Foundations.bend as F

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


# Raw prepared bodies start with tag7; ordinary canonical requests cannot.
# These are consequences of the unchanged Protocol, not an extension of it.

def starts_seven(result: Maybe<&2, List<&2, U32>>) -> Bool:
  match result:
    case Some{Con{head, tail}}: U32.is_eq(head, 7)
    case _: False{}

def prefix_six_excludes_seven(size: Maybe<&2, List<&2, U32>>, +content: List<&2, U32>,
  +tail: List<&2, U32>, encoded: {P.prefix_size(6, size, content) == Some{Con{7, tail}} : Maybe<&2, List<&2, U32>>}) -> Empty:
  match size:
    case None{}:
      F.none_negative_some(List<&2, U32>, Con{7, tail}, encoded)
    case Some{header}:
      F.false_negative_true(Equal.cong(Maybe<&2, List<&2, U32>>, Bool,
        result => starts_seven(result),
        Some{Con{6, B.concatenate(header, content)}}, Some{Con{7, tail}}, encoded))

def record_cases_excludes_seven(name: Maybe<&2, List<&2, U32>>,
  value: Maybe<&2, List<&2, U32>>, rest: P.Partial, +tail: List<&2, U32>,
  encoded: {P.finalize(P.record_cases(name, value, rest)) == Some{Con{7, tail}} : Maybe<&2, List<&2, U32>>}) -> Empty:
  match name value rest:
    case None{} _ _:
      F.none_negative_some(List<&2, U32>, Con{7, tail}, encoded)
    case Some{nb} None{} _:
      F.none_negative_some(List<&2, U32>, Con{7, tail}, encoded)
    case Some{nb} Some{vb} P.Record{n, payload}:
      prefix_six_excludes_seven(B.length64(1n+n), B.concatenate(nb, B.concatenate(vb, payload)), tail, encoded)
    case Some{nb} Some{vb} P.Impossible{}:
      F.none_negative_some(List<&2, U32>, Con{7, tail}, encoded)
    case Some{nb} Some{vb} P.Atom{payload}:
      F.none_negative_some(List<&2, U32>, Con{7, tail}, encoded)
    case Some{nb} Some{vb} P.ListFrame{n, payload}:
      F.none_negative_some(List<&2, U32>, Con{7, tail}, encoded)

def release_encoding_guard(valid: Bool, +result: Maybe<&2, List<&2, U32>>, +tail: List<&2, U32>,
  encoded: {P.encode_cases(valid, result) == Some{Con{7, tail}} : Maybe<&2, List<&2, U32>>}) ->
  {result == Some{Con{7, tail}} : Maybe<&2, List<&2, U32>>}:
  match valid:
    case True{}: encoded
    case False{}:
      L.ex_false({result == Some{Con{7, tail}} : Maybe<&2, List<&2, U32>>},
        F.none_negative_some(List<&2, U32>, Con{7, tail}, encoded))

law record_encoding_excludes_prepared_tag:
  for +name: String
  for +value: D.Value
  for +rest: D.Value
  for +tail: List<&2, U32>
  P.Encoding(D.VRecord{name, value, rest}, Con{7, tail}) -> Empty
def record_encoding_excludes_prepared_tag(name, value, rest, tail, encoded):
  record_cases_excludes_seven(P.text(name), P.finalize(P.encode_partial(value)), P.encode_partial(rest), tail,
    release_encoding_guard(D.value_valid(D.VRecord{name, value, rest}),
      P.finalize(P.record_cases(P.text(name), P.finalize(P.encode_partial(value)), P.encode_partial(rest))), tail, encoded))

law ordinary_request_encoding_excludes_prepared_tag:
  for +request: P.Request
  for +tail: List<&2, U32>
  P.Encoding(P.request_value(request), Con{7, tail}) -> Empty
def ordinary_request_encoding_excludes_prepared_tag(request, tail, encoded):
  match request:
    case P.Request{credential, code, arguments, proof}:
      record_encoding_excludes_prepared_tag("arguments", arguments,
        D.VRecord{"code", D.VText{code}, D.VRecord{"credential", D.VText{credential},
          D.VRecord{"proof", D.VText{proof}, D.VRecordEmpty{}}}}, tail, encoded)

def process_body(disposition: X.Disposition) -> List<&2, U32>:
  match disposition:
    case X.ProcessBody{bytes}: bytes
    case _: Nil{}

# If actual reception exposes the raw tag7 body, no ordinary RequestReceived
# witness exists for the same scenario, even with valid framing and limits.
law prepared_raw_body_has_no_ordinary_request_received:
  for -world: Nat
  for -configuration: S.Configuration
  for -state: D.State
  for -input: X.Reception
  for +request: P.Request
  for +tail: List<&2, U32>
  for processing: {X.decide_reception(configuration, input) == X.ProcessBody{Con{7, tail}} : X.Disposition}
  I.RequestReceived(I.Serve{world, configuration, state, input}, request) -> Empty
def prepared_raw_body_has_no_ordinary_request_received(world, configuration, state, input, request, tail, processing, received):
  match received:
    case (+bytes, L.Both{disposition, encoded}):
      ordinary_request_encoding_excludes_prepared_tag(request, tail,
        Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(P.request_value(request)), Some{bytes}, Some{Con{7, tail}},
          encoded,
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, bs => Some{bs}, bytes, Con{7, tail},
            Equal.cong(X.Disposition, List<&2, U32>, process_body, X.ProcessBody{bytes}, X.ProcessBody{Con{7, tail}},
              Equal.trans(X.Disposition, X.ProcessBody{bytes}, X.decide_reception(configuration, input), X.ProcessBody{Con{7, tail}},
                Equal.sym(X.Disposition, X.decide_reception(configuration, input), X.ProcessBody{bytes}, disposition), processing)))))

# Law7's ordinary authentication response cannot justify this raw scenario.
law prepared_raw_authentication_has_no_ordinary_justification:
  for -environment: I.Environment
  for -native: String
  for -world: Nat
  for -configuration: S.Configuration
  for -state: D.State
  for -input: X.Reception
  for -time: Nat
  for +tail: List<&2, U32>
  for processing: {X.decide_reception(configuration, input) == X.ProcessBody{Con{7, tail}} : X.Disposition}
  I.ResponseJustified(S.response_error(S.Authentication{}), environment, native,
    I.Serve{world, configuration, state, input}, time) -> Empty
def prepared_raw_authentication_has_no_ordinary_justification(environment, native, world, configuration, state, input, time, tail, processing, justified):
  match justified:
    case (+request, L.Both{authenticated, received}):
      prepared_raw_body_has_no_ordinary_request_received(world, configuration, state, input, request, tail, processing, received)
