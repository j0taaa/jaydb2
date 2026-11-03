# Actual body quantity before interpreting internal lengths.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ../src/Input.bend as E
import ../src/Request.bend as Q
import ./CodecTrace.bend as Trace

law body_admitted_preserves_result_of_codec:
  for +bs: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {E.read_message(Some{ceiling}, bs, s) == E.message(C.decode(bs, ceiling), s) : E.PreAuthentication}
def body_admitted_preserves_result_of_codec(bs, body, ceiling, s, measured, fits):
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bs)), Some{body}, measured) :
    {E.message_measure(_, bs, ceiling, s) == E.message(C.decode(bs, ceiling), s) : E.PreAuthentication}
  %Equal.sym(Bool, C.less_equal64(body, ceiling), True{}, fits) :
    {E.message_fits(_, bs, ceiling, s) == E.message(C.decode(bs, ceiling), s) : E.PreAuthentication}
  {==}

law body_real_above_of_ceiling_produces_limit:
  for +bs: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for above: {C.less_equal64(body, ceiling) == False{} : Bool}
  {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
def body_real_above_of_ceiling_produces_limit(bs, body, ceiling, s, measured, above):
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bs)), Some{body}, measured) :
    {E.message_measure(_, bs, ceiling, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
  %Equal.sym(Bool, C.less_equal64(body, ceiling), False{}, above) :
    {E.message_fits(_, bs, ceiling, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
  {==}

law body_real_negative_representable_produces_limit:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == None{} : Maybe<&2, B.Number64>}
  {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
def body_real_negative_representable_produces_limit(bs, ceiling, s, measured):
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bs)), None{}, measured) :
    {E.message_measure(_, bs, ceiling, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
  {==}

def accepts_preserves(+bs: List<&2, U32>, +ceiling: B.Number64, +s: D.State,
  -v: D.Value, checked: Trace.InputChecked<B.nat64(B.length(bs)), bs, ceiling, v>) ->
  {E.read_message(Some{ceiling}, bs, s) == E.message(C.decode(bs, ceiling), s) : E.PreAuthentication}:
  match checked:
    case Trace.Checked{body, measured, fits, octets, execution_trace}:
      body_admitted_preserves_result_of_codec(bs, body, ceiling, s, measured, fits)

# Actual acceptance already supplies measure and admissibility; requires no new
# hypotheses in existing canonical-composition APIs.
law decoding_accepts_preserves_message:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +s: D.State
  for -v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  {E.read_message(Some{ceiling}, bs, s) == E.message(C.decode(bs, ceiling), s) : E.PreAuthentication}
def decoding_accepts_preserves_message(bs, ceiling, s, v, accepted):
  accepts_preserves(bs, ceiling, s, v,
    Trace.acceptance_requires_body_representable_octets_and_limit(bs, ceiling, v, accepted))

law limit_internal_in_body_admitted_and_input:
  for +bs: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for internal: {C.decode(bs, ceiling) == C.Limit{} : C.Outcome}
  {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Input{}} : E.PreAuthentication}
def limit_internal_in_body_admitted_and_input(bs, body, ceiling, s, measured, fits, internal):
  Equal.trans(E.PreAuthentication, E.read_message(Some{ceiling}, bs, s),
    E.message(C.decode(bs, ceiling), s), E.ErrorMessage{S.Input{}},
    body_admitted_preserves_result_of_codec(bs, body, ceiling, s, measured, fits),
    Equal.cong(C.Outcome, E.PreAuthentication, r => E.message(r, s), C.decode(bs, ceiling), C.Limit{}, internal))

# Characterizes the CAUSE of Limit output without receiving that cause as a premise.
def CountExceeded(measure: Maybe<&2, B.Number64>, -ceiling: B.Number64) -> Type:
  match measure:
    case None{}:
      Unit
    case Some{body}:
      {C.less_equal64(body, ceiling) == False{} : Bool}

def WithoutLimit(pre: E.PreAuthentication) -> Type:
  match pre:
    case E.ErrorMessage{S.Limit{}}:
      Empty
    case _:
      Unit

def envelope_without_limit(q: Maybe<&2, P.Request>, -s: D.State) -> WithoutLimit(E.envelope(q, s)):
  match q:
    case None{}:
      Unit{}
    case Some{r}:
      Unit{}

law message_of_codec_never_creates_limit_of_resource:
  for result: C.Outcome
  for -s: D.State
  WithoutLimit(E.message(result, s))
def message_of_codec_never_creates_limit_of_resource(result, s):
  match result:
    case C.Input{}:
      Unit{}
    case C.Limit{}:
      Unit{}
    case C.Decoded{v}:
      envelope_without_limit(Q.extract(v), s)

def cause_in_size(fits: Bool, +bs: List<&2, U32>, +ceiling: B.Number64, +s: D.State,
  failure: {E.message_fits(fits, bs, ceiling, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}) ->
  {fits == False{} : Bool}:
  match fits:
    case False{}:
      {==}
    case True{}:
      L.ex_false({True{} == False{} : Bool},
        (%failure : WithoutLimit(_)
          message_of_codec_never_creates_limit_of_resource(C.decode(bs, ceiling), s)))

def cause_in_measure(measure: Maybe<&2, B.Number64>, +bs: List<&2, U32>, +ceiling: B.Number64, +s: D.State,
  failure: {E.message_measure(measure, bs, ceiling, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}) ->
  CountExceeded(measure, ceiling):
  match measure:
    case None{}:
      Unit{}
    case Some{body}:
      cause_in_size(C.less_equal64(body, ceiling), bs, ceiling, s, failure)

law message_limit_requires_excess_of_count_real:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +s: D.State
  for failure: {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
  CountExceeded(B.nat64(B.length(bs)), ceiling)
def message_limit_requires_excess_of_count_real(bs, ceiling, s, failure):
  cause_in_measure(B.nat64(B.length(bs)), bs, ceiling, s, failure)
