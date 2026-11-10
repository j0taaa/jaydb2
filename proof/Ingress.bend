# Composed M4: complete ordinary bodies and prepared selection reach Core.
# Each wrapper classifies the ACTUAL computed pre-authentication/selection
# result and then applies the universal Core theorem to the exact request.
import Base
import ../contract/Theorems.bend as C
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../contract/PreparedRegistry.bend as G
import ../src/Codec.bend as Codec
import ../src/Input.bend as Input
import ../src/Request.bend as Request
import ../src/Gate.bend as K
import ../src/Resolve.bend as Resolve
import ./Foundations.bend as F
import ./Preparation.bend as Q
import ./Call.bend as Call
import ./CodecSumsOrder.bend as O
import ./CoreClauses.bend as Core

# A fixed denial is framed within the response limit and keeps the root.
def denial(k: C.Clause, +status: S.Status, -e: D.Schema, -laws: S.Laws, +lim: S.Limits, -amb: String,
  +s: D.State, limits: {R.limits_all_valid(lim) == True{} : Bool}, error: Q.Error(status)) ->
  C.Denial(k, S.Configuration{e, laws, lim, amb}, s, S.response_error(status)):
  match k:
    case C.Admitted{}: Core.early_error(status, e, laws, lim, amb, s, limits, error)
    case C.Safe{}: Unit{}
    case C.Completed{}: Unit{}
    case C.Progressing{}: Unit{}

# ---------------------------------------------------------------------------
# Ordinary body ingress.

# What read_message can return for a representable message limit.
def Received(input: Input.PreAuthentication, -s: D.State) -> Type:
  match input:
    case Input.InputReady{state, r}: {state == s : D.State}
    case Input.ErrorMessage{status}: Q.Error(status)
    case Input.ErrorTransport{}: Empty

def received_envelope(request: Maybe<&2, P.Request>, +s: D.State) ->
  Received(Input.envelope(request, s), s):
  match request:
    case None{}: Unit{}
    case Some{r}: {==}

def received_decoded(result: Codec.Outcome, +s: D.State) ->
  Received(Input.message(result, s), s):
  match result:
    case Codec.Decoded{v}: received_envelope(Request.extract(v), s)
    case Codec.Input{}: Unit{}
    case Codec.Limit{}: Unit{}

def received_fits(fits: Bool, +bytes: List<&2, U32>, +limit: B.Number64, +s: D.State) ->
  Received(Input.message_fits(fits, bytes, limit, s), s):
  match fits:
    case False{}: Unit{}
    case True{}: received_decoded(Codec.decode(bytes, limit), s)

def received_measure(measure: Maybe<&2, B.Number64>, +bytes: List<&2, U32>, +limit: B.Number64,
  +s: D.State) -> Received(Input.message_measure(measure, bytes, limit, s), s):
  match measure:
    case None{}: Unit{}
    case Some{body}: received_fits(Codec.less_equal64(body, limit), bytes, limit, s)

def received_represented(-msg: Nat, represented: O.NumberRepresented<B.nat64(msg)>,
  +bytes: List<&2, U32>, +s: D.State) -> Received(Input.read_message(B.nat64(msg), bytes, s), s):
  match represented:
    case O.Represented{+number, exact}:
      %Equal.sym(Maybe<&2, B.Number64>, B.nat64(msg), Some{number}, exact) :
        Received(Input.read_message(_, bytes, s), s)
      received_measure(B.nat64(B.length(bytes)), bytes, number, s)

def received_message(lim: S.Limits, +bytes: List<&2, U32>, +s: D.State,
  limits: {R.limits_all_valid(lim) == True{} : Bool}) ->
  Received(Input.read_message(B.nat64(R.limit_message(lim)), bytes, s), s):
  match lim:
    case S.Limits{+msg, +est, +resp}:
      received_represented(msg,
        Call.represented(msg, F.and_boolean_left(P.representable_result(B.length64(msg)),
          P.representable_result(B.length64(est)),
          F.and_boolean_left(P.representable_result(B.length64(msg)) && P.representable_result(B.length64(est)),
            P.representable_result(B.length64(resp)),
            Q.prefix_limits_all_valid(S.Limits{msg, est, resp}, limits)))),
        bytes, s)

def decoded(k: C.Clause, input: Input.PreAuthentication, +e: D.Schema, laws: S.Laws,
  +lim: S.Limits, +amb: String, +s: D.State, admit: K.Oracle(), received: Received(input, s),
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, s),
  sound: C.DecodedOracleSoundness(input, S.Configuration{e, laws, lim, amb}, admit)) ->
  C.DecodedCore(k, input, S.Configuration{e, laws, lim, amb}, s, admit):
  match input:
    case Input.InputReady{state, +r}:
      L.Both{received, Core.core_theorem()(k, S.Configuration{e, laws, lim, amb}, s, r, admit,
        configured, valid, sound)}
    case Input.ErrorMessage{+status}:
      denial(k, status, e, laws, lim, amb, s, Core.limits_valid(e, laws, lim, amb, configured), received)
    case Input.ErrorTransport{}:
      match received:

def ingress(k: C.Clause, c: S.Configuration, +s: D.State, +body: List<&2, U32>, admit: K.Oracle(),
  +configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  sound: C.IngressOracleSoundness(c, s, body, admit)) -> C.IngressCore(k, c, s, body, admit):
  match c:
    case S.Configuration{+e, laws, +lim, +amb}:
      decoded(k, Input.read_message(B.nat64(R.limit_message(lim)), body, s), e, laws, lim, amb, s, admit,
        received_message(lim, body, s, Core.limits_valid(e, laws, lim, amb, configured)),
        configured, valid, sound)

def ingress_theorem() -> C.IngressTheorem():
  k => c => +s => +body => admit => configured => valid => sound =>
    ingress(k, c, s, body, admit, configured, valid, sound)

# ---------------------------------------------------------------------------
# Direct and prepared execution share Core after the actual selection.

# What Resolve.select can return: a fixed error status, or a request.
def Chosen(selection: Resolve.Selection) -> Type:
  match selection:
    case Resolve.Denied{status}: Q.Error(status)
    case Resolve.Selected{r}: Unit

def chosen_found(result: Maybe<&2, G.Entry>, raw: P.Request) -> Chosen(Resolve.found(result, raw)):
  match result:
    case None{}: Unit{}
    case Some{entry}: Unit{}

def chosen_checked(empty: Bool, +instance: String, entries: List<&2, G.Entry>, +raw: P.Request) ->
  Chosen(Resolve.proof_checked(empty, instance, entries, raw)):
  match empty:
    case False{}: Unit{}
    case True{}: chosen_found(G.lookup(instance, K.code(raw), entries), raw)

def chosen_authenticated(authentication: Maybe<&2, D.Context>, +instance: String,
  entries: List<&2, G.Entry>, +raw: P.Request) ->
  Chosen(Resolve.authenticated(authentication, instance, entries, raw)):
  match authentication:
    case None{}: Unit{}
    case Some{ctx}: chosen_checked(String.eq(Resolve.proof(raw), ""), instance, entries, raw)

def chosen(+instance: String, +s: D.State, entries: List<&2, G.Entry>, input: Resolve.Input) ->
  Chosen(Resolve.select(instance, s, entries, input)):
  match input:
    case Resolve.Direct{r}: Unit{}
    case Resolve.Registered{+raw}:
      chosen_authenticated(D.authenticate(s, K.credential(raw)), instance, entries, raw)

def selected(k: C.Clause, selection: Resolve.Selection, +e: D.Schema, laws: S.Laws,
  +lim: S.Limits, +amb: String, +s: D.State, admit: K.Oracle(), choice: Chosen(selection),
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, s),
  sound: C.SelectedOracleSoundness(selection, S.Configuration{e, laws, lim, amb}, admit)) ->
  C.SelectedCore(k, selection, S.Configuration{e, laws, lim, amb}, s, admit):
  match selection:
    case Resolve.Denied{+status}:
      denial(k, status, e, laws, lim, amb, s, Core.limits_valid(e, laws, lim, amb, configured), choice)
    case Resolve.Selected{+r}:
      Core.core_theorem()(k, S.Configuration{e, laws, lim, amb}, s, r, admit, configured, valid, sound)

def unified(k: C.Clause, c: S.Configuration, +s: D.State, +entries: List<&2, G.Entry>,
  +input: Resolve.Input, admit: K.Oracle(),
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  sound: C.ResolvedOracleSoundness(c, s, entries, input, admit)) -> C.UnifiedCore(k, c, s, entries, input, admit):
  match c:
    case S.Configuration{+e, laws, +lim, +amb}:
      selected(k, Resolve.select(amb, s, entries, input), e, laws, lim, amb, s, admit,
        chosen(amb, s, entries, input), configured, valid, sound)

def unified_core_theorem() -> C.UnifiedCoreTheorem():
  k => c => +s => +entries => +input => admit => configured => valid => sound =>
    unified(k, c, s, entries, input, admit, configured, valid, sound)
