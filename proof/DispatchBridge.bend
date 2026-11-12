# Every host early reply is the exact early branch of the shared decoder and
# Gate/Resolve composition, on the same current root and original body.
import Base
import ../src/LimitWords.bend as LimitWords
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../contract/Theorems.bend as T
import ../contract/PreparedRegistry.bend as Registry
import ../src/Dispatch.bend as Dispatch
import ../src/Input.bend as Input
import ../src/Messages.bend as Messages
import ../src/Gate.bend as Gate
import ../src/Worker.bend as W
import ../src/Resolve.bend as Resolve
import ../src/Transport.bend as Transport
import ../src/Execution.bend as X
import ../src/Core.bend as Core
import ../src/Generate.bend as Generate
import ./CoreClauses.bend as Clauses
import ./Preparation.bend as Preparation
import ./Ingress.bend as Ingress

# On all public envelopes a ready route has a nonzero, recognized tag.
type Tag<-tag: U32> is Type:
  DirectTag{same: {tag == 1 : U32}}
  PrepareTag{same: {tag == 3 : U32}}
  ExecuteTag{same: {tag == 4 : U32}}
  InvalidateTag{same: {tag == 5 : U32}}

def Routed(input: Dispatch.Routed, -s: D.State) -> Type:
  match input:
    case Dispatch.Routed{tag, Input.InputReady{root, r}}: L.E<Tag<tag>, {root == s : D.State}>
    case Dispatch.Routed{tag, Input.ErrorMessage{status}}: Preparation.Error(status)
    case Dispatch.Routed{tag, Input.ErrorTransport{}}: Unit

def EnvelopeTag(e: Dispatch.Envelope) -> Type:
  match e:
    case Dispatch.Invalid{}: Unit
    case Dispatch.Envelope{tag, body}: Tag<tag>

def opcode_flags_tag(prepare: Bool, execute: Bool, invalidate: Bool, body: List<&2, U32>) ->
  EnvelopeTag(Dispatch.opcode_flags(prepare, execute, invalidate, body)):
  match prepare execute invalidate:
    case True{} _ _: PrepareTag{{==}}
    case False{} True{} _: ExecuteTag{{==}}
    case False{} False{} True{}: InvalidateTag{{==}}
    case False{} False{} False{}: Unit{}

def prefix_tag(extension: Bool, +first: U32, rest: List<&2, U32>) ->
  EnvelopeTag(Dispatch.prefix(extension, first, rest)):
  match extension rest:
    case True{} Con{+op, body}: opcode_flags_tag(U32.is_eq(op, 0), U32.is_eq(op, 1), U32.is_eq(op, 2), body)
    case True{} Nil{}: Unit{}
    case False{} rest: DirectTag{{==}}

def envelope_tag(body: List<&2, U32>) -> EnvelopeTag(Dispatch.envelope(body)):
  match body:
    case Con{+first, rest}: prefix_tag(U32.is_eq(first, 7), first, rest)
    case Nil{}: DirectTag{{==}}

def decoded_route(tag: U32, input: Input.PreAuthentication, -s: D.State,
  tagged: Tag<tag>, received: Ingress.Received(input, s)) -> Routed(Dispatch.Routed{tag, input}, s):
  match input:
    case Input.InputReady{root, r}: L.Both{tagged, received}
    case Input.ErrorMessage{status}: received
    case Input.ErrorTransport{}: match received:

def envelope(e: Dispatch.Envelope, +s: D.State, +limits: S.Limits,
  tagged: EnvelopeTag(e), valid: {R.limits_all_valid(limits) == True{} : Bool}) ->
  Routed(Dispatch.received_envelope(e, s, B.nat64(R.limit_message(limits))), s):
  match e:
    case Dispatch.Invalid{}: Unit{}
    case Dispatch.Envelope{tag, +body}:
      decoded_route(tag, Input.read_message(B.nat64(R.limit_message(limits)), body, s), s,
        tagged, Ingress.received_message(limits, body, s, valid))

def measured(fits: Bool, +body: List<&2, U32>, +s: D.State, +limits: S.Limits,
  valid: {R.limits_all_valid(limits) == True{} : Bool}) ->
  Routed(Dispatch.received_fits(fits, body, s, LimitWords.convert(R.limit_message(limits), Nat.mul(256n, 256n), B.Number64{0, 65536}, LimitWords.common_literal_exact())), s):
  match fits:
    case False{}: Unit{}
    case True{}:
      %Equal.sym(Maybe<&2, B.Number64>, LimitWords.convert(R.limit_message(limits), Nat.mul(256n, 256n), B.Number64{0, 65536}, LimitWords.common_literal_exact()),
        B.nat64(R.limit_message(limits)), LimitWords.convert_equals_reference(R.limit_message(limits), Nat.mul(256n, 256n), B.Number64{0, 65536}, LimitWords.common_literal_exact())) :
        Routed(Dispatch.received_envelope(Dispatch.envelope(body), s, _), s)
      envelope(Dispatch.envelope(body), s, limits, envelope_tag(body), valid)

# This is exactly the corresponding decoded Ingress branch (direct/prepare)
# or Unified selection branch (execute/invalidate) before external admission.
def reference_ready(~c: S.Configuration, +s: D.State, entries: List<&2, Registry.Entry>,
  tag: U32, r: P.Request, admit: Gate.Oracle()) -> X.Iteration:
  match tag:
    case 4: W.unified(c, s, entries, Resolve.Registered{r}, admit)
    case 5: W.unified(c, s, entries, Resolve.Registered{r}, admit)
    case _: W.decoded(c, s, Input.InputReady{s, r}, admit)

def reference(~c: S.Configuration, +s: D.State, entries: List<&2, Registry.Entry>,
  routed: Dispatch.Routed, admit: Gate.Oracle()) -> X.Iteration:
  match routed:
    case Dispatch.Routed{tag, Input.InputReady{root, r}}: reference_ready(c, root, entries, tag, r, admit)
    case Dispatch.Routed{tag, input}: W.decoded(c, s, input, admit)

# The implication inspects the actual bytes Rust tests, not a freely supplied
# status. Its evidence includes bounded framing, unchanged root, and equality
# to the corresponding Ingress/Unified early branch.
def Reply(output: List<&2, U32>, -c: S.Configuration, -s: D.State, -ref: X.Iteration) -> Type:
  match output:
    case Con{0, bytes}:
      &status: S.Status -> L.E<T.Early(c, s, S.response_error(status)),
        L.E<{P.frame(S.response_value(S.response_error(status))) == Some{bytes} : Maybe<&2, List<&2, U32>>},
          {ref == X.FinishOutput{Con{0, bytes}} : X.Iteration}>>
    case _: Unit

def prefix_1(encoded: Maybe<&2, List<&2, U32>>, -c: S.Configuration, -s: D.State, -ref: X.Iteration) ->
  Reply(Dispatch.retag(1, Messages.prefix(1, encoded)), c, s, ref):
  match encoded:
    case None{}: Unit{}
    case Some{bs}: Unit{}

def prefix_3(encoded: Maybe<&2, List<&2, U32>>, -c: S.Configuration, -s: D.State, -ref: X.Iteration) ->
  Reply(Dispatch.retag(3, Messages.prefix(1, encoded)), c, s, ref):
  match encoded:
    case None{}: Unit{}
    case Some{bs}: Unit{}

def prefix_4(encoded: Maybe<&2, List<&2, U32>>, -c: S.Configuration, -s: D.State, -ref: X.Iteration) ->
  Reply(Dispatch.retag(4, Messages.prefix(1, encoded)), c, s, ref):
  match encoded:
    case None{}: Unit{}
    case Some{bs}: Unit{}

def prefix_5(encoded: Maybe<&2, List<&2, U32>>, -c: S.Configuration, -s: D.State, -ref: X.Iteration) ->
  Reply(Dispatch.retag(5, Messages.prefix(1, encoded)), c, s, ref):
  match encoded:
    case None{}: Unit{}
    case Some{bs}: Unit{}

def success_prefix(tag: U32, encoded: Maybe<&2, List<&2, U32>>, -c: S.Configuration,
  -s: D.State, -ref: X.Iteration, tagged: Tag<tag>) ->
  Reply(Dispatch.retag(tag, Messages.prefix(1, encoded)), c, s, ref):
  match tagged:
    case DirectTag{same}:
      %Equal.sym(U32, tag, 1, same) : Reply(Dispatch.retag(_, Messages.prefix(1, encoded)), c, s, ref)
      prefix_1(encoded, c, s, ref)

    case PrepareTag{same}:
      %Equal.sym(U32, tag, 3, same) : Reply(Dispatch.retag(_, Messages.prefix(1, encoded)), c, s, ref)
      prefix_3(encoded, c, s, ref)

    case ExecuteTag{same}:
      %Equal.sym(U32, tag, 4, same) : Reply(Dispatch.retag(_, Messages.prefix(1, encoded)), c, s, ref)
      prefix_4(encoded, c, s, ref)

    case InvalidateTag{same}:
      %Equal.sym(U32, tag, 5, same) : Reply(Dispatch.retag(_, Messages.prefix(1, encoded)), c, s, ref)
      prefix_5(encoded, c, s, ref)

def success_instance(tag: U32, instance: Maybe<&2, String>, +id: String, +code: String,
  +proof: String, +links: String, -c: S.Configuration, -s: D.State, -ref: X.Iteration, tagged: Tag<tag>) ->
  Reply(Dispatch.retag(tag, Messages.instance_ready(instance, id, code, proof, links)), c, s, ref):
  match instance:
    case None{}: Unit{}
    case Some{source}: success_prefix(tag,
      Messages.join(B.utf8(id), Messages.join(B.utf8(code), Messages.join(B.utf8(proof),
        Transport.join(B.utf8(source), B.utf8(links))))), c, s, ref, tagged)

def success(tag: U32, state: D.State, r: P.Request, +ctx: D.Context,
  -c: S.Configuration, -s: D.State, -ref: X.Iteration, tagged: Tag<tag>) ->
  Reply(Dispatch.retag(tag, Messages.authentication(Input.Received{state, r, ctx})), c, s, ref):
  match r:
    case P.Request{credential, +code, +args, +proof}:
      success_instance(tag, Generate.instance(ctx, args), Messages.principal(ctx), code, proof, Generate.links(code), c, s, ref, tagged)

def error_fixed(+tag: U32, +status: S.Status, -c: S.Configuration, +s: D.State,
  -ref: X.Iteration, +same: {ref == X.result(Gate.early(S.response_error(status), s)) : X.Iteration},
  early: T.Early(c, s, S.response_error(status)),
  keep: @bytes: List<&2, U32> -> {X.conclude(Core.Conclusion{s, S.response_error(status), bytes}) == X.FinishOutput{Con{0, bytes}} : X.Iteration}) ->
  Reply(Dispatch.retag(tag, Messages.error(status)), c, s, ref):
  match early:
    case (+bytes, L.Both{+concluded, L.Both{+framed, fits}}):
      %Equal.sym(Maybe<&2, List<&2, U32>>, P.frame(S.response_value(S.response_error(status))), Some{bytes}, framed) :
        Reply(Dispatch.retag(tag, Messages.prefix(0, _)), c, s, ref)
      (status, L.Both{(bytes, L.Both{concluded, L.Both{framed, fits}}), L.Both{framed,
        Equal.trans(X.Iteration, ref, X.result(Gate.early(S.response_error(status), s)), X.FinishOutput{Con{0, bytes}}, same,
          Equal.trans(X.Iteration, X.result(Gate.early(S.response_error(status), s)), X.conclude(Core.Conclusion{s, S.response_error(status), bytes}), X.FinishOutput{Con{0, bytes}},
            Equal.cong(Maybe<&2, Core.Conclusion>, X.Iteration, X.result, Gate.early(S.response_error(status), s), Some{Core.Conclusion{s, S.response_error(status), bytes}}, concluded), keep(bytes)))}})

def early(c: S.Configuration, +s: D.State, +status: S.Status,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, error: Preparation.Error(status)) ->
  T.Early(c, s, S.response_error(status)):
  match c:
    case S.Configuration{schema, laws, lim, instance}: Clauses.early_error(status, schema, laws, lim, instance, s, limits, error)

def error(~c: S.Configuration, +tag: U32, +status: S.Status, +s: D.State,
  -ref: X.Iteration, same: {ref == X.result(Gate.early(S.response_error(status), s)) : X.Iteration},
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, invalid: Preparation.Error(status)) ->
  Reply(Dispatch.retag(tag, Messages.error(status)), c, s, ref):
  match status:
    case S.Success{}: match invalid:
    case S.Refusal{}: match invalid:
    case S.Input{}: error_fixed(tag, S.Input{}, c, s, ref, same, early(c, s, S.Input{}, limits, Unit{}), bytes => {==})
    case S.Authentication{}: error_fixed(tag, S.Authentication{}, c, s, ref, same, early(c, s, S.Authentication{}, limits, Unit{}), bytes => {==})
    case S.Certificate{}: error_fixed(tag, S.Certificate{}, c, s, ref, same, early(c, s, S.Certificate{}, limits, Unit{}), bytes => {==})
    case S.DataError{}: error_fixed(tag, S.DataError{}, c, s, ref, same, early(c, s, S.DataError{}, limits, Unit{}), bytes => {==})
    case S.Limit{}: error_fixed(tag, S.Limit{}, c, s, ref, same, early(c, s, S.Limit{}, limits, Unit{}), bytes => {==})
    case S.Failure{}: error_fixed(tag, S.Failure{}, c, s, ref, same, early(c, s, S.Failure{}, limits, Unit{}), bytes => {==})

def proof_4(~c: S.Configuration, empty: Bool, +s: D.State, +entries: List<&2, Registry.Entry>,
  +r: P.Request, +ctx: D.Context, admit: Gate.Oracle(),
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.retag(4, Messages.authentication(Dispatch.proof_checked(empty, Input.Received{s, r, ctx}))), c, s,
    W.selected(Resolve.proof_checked(empty, S.environment(c), entries, r), c, s, admit)):
  match empty:
    case False{}: error(c, 4, S.Input{}, s, X.result(Gate.early(S.response_error(S.Input{}), s)), {==}, limits, Unit{})
    case True{}: success(4, s, r, ctx, c, s, W.selected(Resolve.proof_checked(True{}, S.environment(c), entries, r), c, s, admit), ExecuteTag{{==}})

def proof_5(~c: S.Configuration, empty: Bool, +s: D.State, +entries: List<&2, Registry.Entry>,
  +r: P.Request, +ctx: D.Context, admit: Gate.Oracle(),
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.retag(5, Messages.authentication(Dispatch.proof_checked(empty, Input.Received{s, r, ctx}))), c, s,
    W.selected(Resolve.proof_checked(empty, S.environment(c), entries, r), c, s, admit)):
  match empty:
    case False{}: error(c, 5, S.Input{}, s, X.result(Gate.early(S.response_error(S.Input{}), s)), {==}, limits, Unit{})
    case True{}: success(5, s, r, ctx, c, s, W.selected(Resolve.proof_checked(True{}, S.environment(c), entries, r), c, s, admit), InvalidateTag{{==}})

def authenticated_reference(~c: S.Configuration, +s: D.State, entries: List<&2, Registry.Entry>,
  tag: U32, +r: P.Request, admit: Gate.Oracle(), auth: Maybe<&2, D.Context>) -> X.Iteration:
  match tag:
    case 4: W.selected(Resolve.authenticated(auth, S.environment(c), entries, r), c, s, admit)
    case 5: W.selected(Resolve.authenticated(auth, S.environment(c), entries, r), c, s, admit)
    case _: W.entered(Gate.authenticated(c, auth, r, s, admit), s)

def authenticated_1(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  +r: P.Request, admit: Gate.Oracle(), auth: Maybe<&2, D.Context>,
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.retag(1, Messages.authentication(Dispatch.validated(1, Input.identity(auth, s, r)))), c, s,
    authenticated_reference(c, s, entries, 1, r, admit, auth)):
  match auth:
    case None{}: error(c, 1, S.Authentication{}, s, X.result(Gate.early(S.response_error(S.Authentication{}), s)), {==}, limits, Unit{})
    case Some{+ctx}: success(1, s, r, ctx, c, s, W.entered(Gate.authenticated(c, Some{ctx}, r, s, admit), s), DirectTag{{==}})

def authenticated_3(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  +r: P.Request, admit: Gate.Oracle(), auth: Maybe<&2, D.Context>,
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.retag(3, Messages.authentication(Dispatch.validated(3, Input.identity(auth, s, r)))), c, s,
    authenticated_reference(c, s, entries, 3, r, admit, auth)):
  match auth:
    case None{}: error(c, 3, S.Authentication{}, s, X.result(Gate.early(S.response_error(S.Authentication{}), s)), {==}, limits, Unit{})
    case Some{+ctx}: success(3, s, r, ctx, c, s, W.entered(Gate.authenticated(c, Some{ctx}, r, s, admit), s), PrepareTag{{==}})

def authenticated_4(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  +r: P.Request, admit: Gate.Oracle(), auth: Maybe<&2, D.Context>,
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.retag(4, Messages.authentication(Dispatch.validated(4, Input.identity(auth, s, r)))), c, s,
    authenticated_reference(c, s, entries, 4, r, admit, auth)):
  match auth:
    case None{}: error(c, 4, S.Authentication{}, s, X.result(Gate.early(S.response_error(S.Authentication{}), s)), {==}, limits, Unit{})
    case Some{+ctx}: proof_4(c, String.eq(Resolve.proof(r), ""), s, entries, r, ctx, admit, limits)

def authenticated_5(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  +r: P.Request, admit: Gate.Oracle(), auth: Maybe<&2, D.Context>,
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.retag(5, Messages.authentication(Dispatch.validated(5, Input.identity(auth, s, r)))), c, s,
    authenticated_reference(c, s, entries, 5, r, admit, auth)):
  match auth:
    case None{}: error(c, 5, S.Authentication{}, s, X.result(Gate.early(S.response_error(S.Authentication{}), s)), {==}, limits, Unit{})
    case Some{+ctx}: proof_5(c, String.eq(Resolve.proof(r), ""), s, entries, r, ctx, admit, limits)

def ready_1(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  r: P.Request, admit: Gate.Oracle(), limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.authenticated(Dispatch.Routed{1, Input.InputReady{s, r}}), c, s,
    reference(c, s, entries, Dispatch.Routed{1, Input.InputReady{s, r}}, admit)):
  match r:
    case P.Request{+credential, code, args, proof}:
      authenticated_1(c, s, entries, P.Request{credential, code, args, proof}, admit, D.authenticate(s, credential), limits)

def ready_3(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  r: P.Request, admit: Gate.Oracle(), limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.authenticated(Dispatch.Routed{3, Input.InputReady{s, r}}), c, s,
    reference(c, s, entries, Dispatch.Routed{3, Input.InputReady{s, r}}, admit)):
  match r:
    case P.Request{+credential, code, args, proof}:
      authenticated_3(c, s, entries, P.Request{credential, code, args, proof}, admit, D.authenticate(s, credential), limits)

def ready_4(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  r: P.Request, admit: Gate.Oracle(), limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.authenticated(Dispatch.Routed{4, Input.InputReady{s, r}}), c, s,
    reference(c, s, entries, Dispatch.Routed{4, Input.InputReady{s, r}}, admit)):
  match r:
    case P.Request{+credential, code, args, proof}:
      authenticated_4(c, s, entries, P.Request{credential, code, args, proof}, admit, D.authenticate(s, credential), limits)

def ready_5(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  r: P.Request, admit: Gate.Oracle(), limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.authenticated(Dispatch.Routed{5, Input.InputReady{s, r}}), c, s,
    reference(c, s, entries, Dispatch.Routed{5, Input.InputReady{s, r}}, admit)):
  match r:
    case P.Request{+credential, code, args, proof}:
      authenticated_5(c, s, entries, P.Request{credential, code, args, proof}, admit, D.authenticate(s, credential), limits)

def ready(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>, +tag: U32,
  +r: P.Request, admit: Gate.Oracle(), tagged: Tag<tag>,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.authenticated(Dispatch.Routed{tag, Input.InputReady{s, r}}), c, s,
    reference(c, s, entries, Dispatch.Routed{tag, Input.InputReady{s, r}}, admit)):
  match tagged:
    case DirectTag{same}:
      %Equal.sym(U32, tag, 1, same) :
        Reply(Dispatch.authenticated(Dispatch.Routed{_, Input.InputReady{s, r}}), c, s,
          reference(c, s, entries, Dispatch.Routed{_, Input.InputReady{s, r}}, admit))
      ready_1(c, s, entries, r, admit, limits)
    case PrepareTag{same}:
      %Equal.sym(U32, tag, 3, same) :
        Reply(Dispatch.authenticated(Dispatch.Routed{_, Input.InputReady{s, r}}), c, s,
          reference(c, s, entries, Dispatch.Routed{_, Input.InputReady{s, r}}, admit))
      ready_3(c, s, entries, r, admit, limits)
    case ExecuteTag{same}:
      %Equal.sym(U32, tag, 4, same) :
        Reply(Dispatch.authenticated(Dispatch.Routed{_, Input.InputReady{s, r}}), c, s,
          reference(c, s, entries, Dispatch.Routed{_, Input.InputReady{s, r}}, admit))
      ready_4(c, s, entries, r, admit, limits)
    case InvalidateTag{same}:
      %Equal.sym(U32, tag, 5, same) :
        Reply(Dispatch.authenticated(Dispatch.Routed{_, Input.InputReady{s, r}}), c, s,
          reference(c, s, entries, Dispatch.Routed{_, Input.InputReady{s, r}}, admit))
      ready_5(c, s, entries, r, admit, limits)

def routed(~c: S.Configuration, +s: D.State, +entries: List<&2, Registry.Entry>,
  input: Dispatch.Routed, admit: Gate.Oracle(), shape: Routed(input, s),
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  Reply(Dispatch.authenticated(input), c, s, reference(c, s, entries, input, admit)):
  match input:
    case Dispatch.Routed{tag, Input.ErrorTransport{}}: Unit{}
    case Dispatch.Routed{+tag, Input.ErrorMessage{+status}}:
      error(c, tag, status, s, X.result(Gate.early(S.response_error(status), s)), {==}, limits, shape)
    case Dispatch.Routed{+tag, Input.InputReady{+root, +r}}:
      L.Both{tagged, +same} = shape
      %Equal.sym(D.State, root, s, same) :
        Reply(Dispatch.authenticated(Dispatch.Routed{tag, Input.InputReady{_, r}}), c, s,
          reference(c, s, entries, Dispatch.Routed{tag, Input.InputReady{_, r}}, admit))
      ready(c, s, entries, tag, r, admit, tagged, limits)

def config_limits(c: S.Configuration, configured: {R.configuration_is_valid(c) == True{} : Bool}) ->
  {R.limits_all_valid(S.limits(c)) == True{} : Bool}:
  match c:
    case S.Configuration{schema, laws, limits, instance}: Clauses.limits_valid(schema, laws, limits, instance, configured)

law dispatch_denials_equal_ingress_unified_early:
  for ~c: S.Configuration
  for +s: D.State
  for +state_bytes: List<&2, U32>
  for +packet: List<&2, U32>
  for +body: List<&2, U32>
  for +entries: List<&2, Registry.Entry>
  for admit: Gate.Oracle()
  for parts: {Transport.separate(packet) == Some{Transport.Parts{state_bytes, body}} : Maybe<&2, Transport.Parts>}
  for root: {Dispatch.read_root(state_bytes, S.schema(c), S.limits(c)) == Some{s} : Maybe<&2, D.State>}
  for configured: {R.configuration_is_valid(c) == True{} : Bool}
  Reply(Dispatch.authentication(packet, S.schema(c), S.limits(c)), c, s,
    reference(c, s, entries, Dispatch.received(S.limits(c), body, s), admit))
def dispatch_denials_equal_ingress_unified_early(c, s, state_bytes, packet, body, entries, admit, parts, root, configured):
  %Equal.sym(Maybe<&2, Transport.Parts>, Transport.separate(packet), Some{Transport.Parts{state_bytes, body}}, parts) :
    Reply(Dispatch.authenticated(Dispatch.parts(_, S.schema(c), S.limits(c))), c, s,
      reference(c, s, entries, Dispatch.received(S.limits(c), body, s), admit))
  %Equal.sym(Maybe<&2, D.State>, Dispatch.read_root(state_bytes, S.schema(c), S.limits(c)), Some{s}, root) :
    Reply(Dispatch.authenticated(Dispatch.rooted(_, body, S.limits(c))), c, s,
      reference(c, s, entries, Dispatch.received(S.limits(c), body, s), admit))
  +limits = config_limits(c, configured)
  routed(c, s, entries, Dispatch.received(S.limits(c), body, s), admit,
    measured(Nat.is_le(B.length(body), R.limit_message(S.limits(c))), body, s, S.limits(c), limits), limits)
