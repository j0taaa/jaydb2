# Soundness of the counted text state, including reconstruction of the
# ORIGINAL count from acceptance, without assuming nat64(length).
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecCounters.bend as N
import ./CodecContent.bend as G
import ./CodecUTF8.bend as U
import ./CodecUTF8InverseText.bend as I
import ./CodecTrace.bend as R
import ./CodecTexts.bend as T
import ./CodecWordsInverse.bend as W
import ../contract/Protocol.bend as P
import ./CodecWordsBE64.bend as H
import ./Codec.bend as V

def end_without_last(e: C.Scalar, q: B.Number64, inverted: String) ->
  {C.finalize(C.store_scalar(e, False{}, False{}, q, inverted, C.Root{})) == C.Input{} : C.Outcome}:
  match e:
    case C.UTFInvalid{}:
      {==}
    case C.Character{cp}:
      {==}
    case C.Partial{u}:
      {==}

def unique_octet_checks_last(last: Bool, +e: C.Scalar, +q: B.Number64,
  +inverted: String, -v: D.Value,
  accepted: {C.finalize(C.store_scalar(e, last, False{}, q, inverted, C.Root{})) == C.Decoded{v} : C.Outcome}) ->
  {last == True{} : Bool}:
  match last:
    case True{}:
      {==}
    case False{}:
      L.ex_false({False{} == True{} : Bool}, R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{}, C.finalize(C.store_scalar(e, False{}, False{}, q, inverted, C.Root{})), C.Decoded{v},
          Equal.sym(C.Outcome, C.finalize(C.store_scalar(e, False{}, False{}, q, inverted, C.Root{})), C.Input{}, end_without_last(e, q, inverted)), accepted)))

law last_scalar_refusal_any_suffix:
  for e: C.Scalar
  for +b: U32
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +inverted: String
  for +body: B.Number64
  for +ceiling: B.Number64
  {C.traverse(Con{b, bs}, body, ceiling, C.store_scalar(e, True{}, False{}, q, inverted, C.Root{})) == C.Input{} : C.Outcome}
def last_scalar_refusal_any_suffix(e, b, bs, q, inverted, body, ceiling):
  match e:
    case C.UTFInvalid{}:
      R.invalid_absorbs_all_suffix(Con{b, bs}, body, ceiling)
    case C.Character{cp}:
      R.ready_refusal_any_octet_extra(b, bs, body, ceiling, D.VText{String.reverse(SCon{Chr{cp}, inverted})})
    case C.Partial{u}:
      R.invalid_absorbs_all_suffix(Con{b, bs}, body, ceiling)

def resume_count_scalar(+e: C.Scalar, +bs: List<&2, U32>, +q: B.Number64,
  +inverted: String, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {C.traverse(bs, body, ceiling, C.store_scalar(e, False{}, False{}, C.decrease64(q), inverted, C.Root{})) == C.Decoded{v} : C.Outcome},
  resume: @u: C.Unicode -> @text: String ->
    {C.traverse(bs, body, ceiling, C.Content{False{}, C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), u, text, C.Root{}}) == C.Decoded{v} : C.Outcome} ->
    {N.last(B.length(bs), C.decrease64(q)) == True{} : Bool}) ->
  {N.last(B.length(bs), C.decrease64(q)) == True{} : Bool}:
  match e:
    case C.UTFInvalid{}:
      L.ex_false({N.last(B.length(bs), C.decrease64(q)) == True{} : Bool}, R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{}, C.traverse(bs, body, ceiling, C.Invalid{}), C.Decoded{v},
          Equal.sym(C.Outcome, C.traverse(bs, body, ceiling, C.Invalid{}), C.Input{}, R.invalid_absorbs_all_suffix(bs, body, ceiling)), accepted)))
    case C.Character{cp}:
      resume(C.Start{}, SCon{Chr{cp}, inverted}, accepted)
    case C.Partial{u}:
      resume(u, inverted, accepted)

def check_count_remaining(last: Bool, +e: C.Scalar, +b: U32, +bs: List<&2, U32>, +q: B.Number64,
  +inverted: String, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {C.traverse(Con{b, bs}, body, ceiling, C.store_scalar(e, last, False{}, C.decrease64(q), inverted, C.Root{})) == C.Decoded{v} : C.Outcome},
  resume: @u: C.Unicode -> @text: String ->
    {C.traverse(Con{b, bs}, body, ceiling, C.Content{False{}, C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q)), u, text, C.Root{}}) == C.Decoded{v} : C.Outcome} ->
    {N.last(B.length(Con{b, bs}), C.decrease64(q)) == True{} : Bool}) ->
  {Bool.not(last) && N.last(B.length(Con{b, bs}), C.decrease64(q)) == True{} : Bool}:
  match last:
    case False{}:
      resume_count_scalar(e, Con{b, bs}, q, inverted, body, ceiling, v, accepted, resume)
    case True{}:
      L.ex_false({False{} == True{} : Bool}, R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{}, C.traverse(Con{b, bs}, body, ceiling, C.store_scalar(e, True{}, False{}, C.decrease64(q), inverted, C.Root{})), C.Decoded{v},
          Equal.sym(C.Outcome, C.traverse(Con{b, bs}, body, ceiling, C.store_scalar(e, True{}, False{}, C.decrease64(q), inverted, C.Root{})), C.Input{},
            last_scalar_refusal_any_suffix(e, b, bs, C.decrease64(q), inverted, body, ceiling)), accepted)))

law content_accepted_checked_all_os_last:
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +u: C.Unicode
  for +inverted: String
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.traverse(bs, body, ceiling, C.Content{False{}, C.one64(q), C.decrease64(q), u, inverted, C.Root{}}) == C.Decoded{v} : C.Outcome}
  {N.last(B.length(bs), q) == True{} : Bool}
def content_accepted_checked_all_os_last(bs, q, u, inverted, body, ceiling, v, accepted):
  match bs:
    case Nil{}:
      L.ex_false({False{} == True{} : Bool}, R.input_negative_decoded(v, accepted))
    case Con{+b, Nil{}}:
      unique_octet_checks_last(C.one64(q), C.step_utf8(u, b), C.decrease64(q), inverted, v, accepted)
    case Con{+b, Con{+x, +rest}}:
      check_count_remaining(C.one64(q), C.step_utf8(u, b), x, rest, q, inverted, C.decrease64(body), C.decrease64(ceiling), v, accepted,
        next => text => e => content_accepted_checked_all_os_last(Con{x, rest}, C.decrease64(q), next, text, C.decrease64(body), C.decrease64(ceiling), v, e))

law content_accepted_reconstructs_count_original:
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +u: C.Unicode
  for +inverted: String
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.traverse(bs, body, ceiling, C.Content{False{}, C.one64(q), C.decrease64(q), u, inverted, C.Root{}}) == C.Decoded{v} : C.Outcome}
  {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>}
def content_accepted_reconstructs_count_original(bs, q, u, inverted, body, ceiling, v, accepted):
  N.last_accepted_reconstruct_to_count_original(B.length(bs), q,
    content_accepted_checked_all_os_last(bs, q, u, inverted, body, ceiling, v, accepted))

def content_accepted_has_bytes(+bs: List<&2, U32>, -q: B.Number64, -u: C.Unicode, -inverted: String,
  -body: B.Number64, -ceiling: B.Number64, -v: D.Value,
  accepted: {C.traverse(bs, body, ceiling, C.Content{False{}, C.one64(q), C.decrease64(q), u, inverted, C.Root{}}) == C.Decoded{v} : C.Outcome}) -> G.NotEmpty(bs):
  match bs:
    case Nil{}:
      R.input_negative_decoded(v, accepted)
    case Con{b, t}:
      Unit{}

type TextCompleted<-t: U.TextValue, -v: D.Value> is Type:
  TextCompleted{text: String,
    value: {v == D.VText{text} : D.Value},
    transduction: {U.finalize_text(t) == Some{text} : Maybe<&2, String>}}

def value_result(r: C.Outcome) -> D.Value:
  match r:
    case C.Decoded{v}:
      v
    case _:
      D.VAbsent{}

def text_finalized_accepted(t: U.TextValue, -v: D.Value,
  accepted: {C.finalize(G.conclude_text(False{}, C.Root{}, t)) == C.Decoded{v} : C.Outcome}) -> TextCompleted<t, v>:
  match t:
    case U.TextInvalid{}:
      L.ex_false(TextCompleted<U.TextInvalid{}, v>, R.input_negative_decoded(v, accepted))
    case U.Reading{C.Start{}, +inverted}:
      TextCompleted{String.reverse(inverted),
        Equal.sym(D.Value, D.VText{String.reverse(inverted)}, v, Equal.cong(C.Outcome, D.Value, r => value_result(r), C.Decoded{D.VText{String.reverse(inverted)}}, C.Decoded{v}, accepted)), {==}}
    case U.Reading{C.Continue{n, cp, minimum}, inverted}:
      L.ex_false(TextCompleted<U.Reading{C.Continue{n, cp, minimum}, inverted}, v>, R.input_negative_decoded(v, accepted))

type ContentDecoded<-bs: List<&2, U32>, -q: B.Number64, -v: D.Value> is Type:
  ContentDecoded{text: String,
    measure: {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>},
    value: {v == D.VText{text} : D.Value},
    bytes: {B.utf8(text) == bs : List<&2, U32>}}

def reencode_text_completed(+bs: List<&2, U32>, -q: B.Number64, -v: D.Value,
  measure: {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>},
  text: TextCompleted<U.traverse_text(bs, U.Reading{C.Start{}, ""}), v>) -> ContentDecoded<bs, q, v>:
  match text:
    case TextCompleted{+s, value, transduction}:
      ContentDecoded{s, measure, value, I.utf8_input_accepts_reencodes_exactly(bs, s, transduction)}

law content_textual_accepted_reconstructs_exactly_os_bytes:
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for +accepted: {C.traverse(bs, body, ceiling, C.Content{False{}, C.one64(q), C.decrease64(q), C.Start{}, "", C.Root{}}) == C.Decoded{v} : C.Outcome}
  ContentDecoded<bs, q, v>
def content_textual_accepted_reconstructs_exactly_os_bytes(bs, q, body, ceiling, v, accepted):
  +measure = content_accepted_reconstructs_count_original(bs, q, C.Start{}, "", body, ceiling, v, accepted)
  +machine = G.content_counted_consume_exactly_o_text(bs, q, body, ceiling, False{}, C.Start{}, "", C.Root{},
    content_accepted_has_bytes(bs, q, C.Start{}, "", body, ceiling, v, accepted), measure)
  result = {(%R.execution_trace_and_execution_integral(bs, R.Frame{body, ceiling, C.Content{False{}, C.one64(q), C.decrease64(q), C.Start{}, "", C.Root{}}}) :
    {_ == C.Decoded{v} : C.Outcome}
    accepted) : {C.finalize(G.process_content(bs, q, body, ceiling, False{}, C.Start{}, "", C.Root{})) == C.Decoded{v} : C.Outcome}}
  reencode_text_completed(bs, q, v, measure,
    text_finalized_accepted(U.traverse_text(bs, U.Reading{C.Start{}, ""}), v,
      (%machine : {C.finalize(_) == C.Decoded{v} : C.Outcome}
        result)))

# Large/Short cannot be hidden by later bytes.
def check_textual_accepts(c: C.Check, +bs: List<&2, U32>, +q: B.Number64,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {C.traverse(bs, body, ceiling, C.open_checked(c, C.TextValue{}, q, C.Root{})) == C.Decoded{v} : C.Outcome}) ->
  {C.traverse(bs, body, ceiling, C.open_variable(C.zero64(q), C.TextValue{}, q, C.Root{})) == C.Decoded{v} : C.Outcome}:
  match c:
    case C.Fits{}:
      accepted
    case C.Short{}:
      L.ex_false({C.traverse(bs, body, ceiling, C.open_variable(C.zero64(q), C.TextValue{}, q, C.Root{})) == C.Decoded{v} : C.Outcome}, R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{}, C.traverse(bs, body, ceiling, C.Invalid{}), C.Decoded{v}, Equal.sym(C.Outcome, C.traverse(bs, body, ceiling, C.Invalid{}), C.Input{}, R.invalid_absorbs_all_suffix(bs, body, ceiling)), accepted)))
    case C.Large{}:
      L.ex_false({C.traverse(bs, body, ceiling, C.open_variable(C.zero64(q), C.TextValue{}, q, C.Root{})) == C.Decoded{v} : C.Outcome}, R.limit_negative_decoded(v,
        Equal.trans(C.Outcome, C.Limit{}, C.traverse(bs, body, ceiling, C.Above{}), C.Decoded{v}, Equal.sym(C.Outcome, C.traverse(bs, body, ceiling, C.Above{}), C.Limit{}, R.above_absorbs_all_suffix(bs, body, ceiling)), accepted)))

def text_open_accepted(zero: Bool, +bs: List<&2, U32>, +q: B.Number64,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  zero_proof: {C.zero64(q) == zero : Bool},
  accepted: {C.traverse(bs, body, ceiling, C.open_variable(zero, C.TextValue{}, q, C.Root{})) == C.Decoded{v} : C.Outcome}) -> ContentDecoded<bs, q, v>:
  match zero bs:
    case False{} _:
      content_textual_accepted_reconstructs_exactly_os_bytes(bs, q, body, ceiling, v, accepted)
    case True{} Nil{}:
      ContentDecoded{"",
        Equal.cong(B.Number64, Maybe<&2, B.Number64>, n => Some{n}, B.Number64{0, 0}, q, Equal.sym(B.Number64, q, B.Number64{0, 0}, N.zero64_only_recognizes_zero(q, zero_proof))),
        Equal.sym(D.Value, D.VText{""}, v, Equal.cong(C.Outcome, D.Value, r => value_result(r), C.Decoded{D.VText{""}}, C.Decoded{v}, accepted)), {==}}
    case True{} Con{+b, +t}:
      L.ex_false(ContentDecoded<Con{b, t}, q, v>, R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{}, C.traverse(Con{b, t}, body, ceiling, C.DecodedReady{D.VText{""}}), C.Decoded{v},
          Equal.sym(C.Outcome, C.traverse(Con{b, t}, body, ceiling, C.DecodedReady{D.VText{""}}), C.Input{}, R.ready_refusal_any_octet_extra(b, t, body, ceiling, D.VText{""})), accepted)))

law conclude_word_textual_accepts_reconstructs_content:
  for +bs: List<&2, U32>
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.traverse(bs, body, ceiling, C.conclude_word(C.TextValue{}, high, low, C.Root{}, body, ceiling)) == C.Decoded{v} : C.Outcome}
  ContentDecoded<bs, B.Number64{high, low}, v>
def conclude_word_textual_accepts_reconstructs_content(bs, high, low, body, ceiling, v, accepted):
  +q = {B.Number64{high, low} : B.Number64}
  text_open_accepted(C.zero64(q), bs, q, body, ceiling, v, {==},
    check_textual_accepts(C.check(C.sum_optional(C.minimum_field(C.TextValue{}, q), C.minimum_stack(C.Root{})), body, ceiling), bs, q, body, ceiling, v, accepted))

law octets_all_valid_of_prefix:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +all_valid: {B.octets_all_valid(B.concatenate(xs, ys)) == True{} : Bool}
  {B.octets_all_valid(xs) == True{} : Bool}
def octets_all_valid_of_prefix(xs, ys, all_valid):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      F.and_boolean_intro(U32.is_le(h, 255), B.octets_all_valid(t),
        F.and_boolean_left(U32.is_le(h, 255), B.octets_all_valid(B.concatenate(t, ys)), all_valid),
        octets_all_valid_of_prefix(t, ys, F.and_boolean_right(U32.is_le(h, 255), B.octets_all_valid(B.concatenate(t, ys)), all_valid)))

# Full canonicity after reconstructing the header and content.
def reencode_text_combined_header(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +bs: List<&2, U32>, -v: D.Value,
  valid: {D.value_valid(v) == True{} : Bool},
  header: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool},
  data: ContentDecoded<bs, B.Number64{W.assemble(a, b, c, d), W.assemble(e, f, g, h)}, v>) ->
  P.Encoding(v, Con{4, B.concatenate([a, b, c, d, e, f, g, h], bs)}):
  match data:
    case ContentDecoded{+s, measure, +value, +bytes}:
      unicode = {(%value : {D.value_valid(_) == True{} : Bool}
        valid) : {D.unicode_valid(s) == True{} : Bool}}
      text_valid = Equal.trans(Bool, B.text_valid(s), D.unicode_valid(s), True{}, T.predicates_of_text_agree(s), unicode)
      measure_text = {(%Equal.sym(List<&2, U32>, B.utf8(s), bs, bytes) :
        {B.nat64(B.length(_)) == Some{B.Number64{W.assemble(a, b, c, d), W.assemble(e, f, g, h)}} : Maybe<&2, B.Number64>}
        measure) : {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{W.assemble(a, b, c, d), W.assemble(e, f, g, h)}} : Maybe<&2, B.Number64>}}
      %Equal.sym(D.Value, v, D.VText{s}, value) : P.Encoding(_, Con{4, B.concatenate([a, b, c, d, e, f, g, h], bs)})
      %W.be64_reencodes_eight_octets_all_valid(a, b, c, d, e, f, g, h, header) :
        {P.encode(D.VText{s}) == Some{Con{4, B.concatenate(_, bs)}} : Maybe<&2, List<&2, U32>>}
      %bytes : {P.encode(D.VText{s}) == Some{Con{4, B.concatenate(B.be64(W.assemble(a, b, c, d), W.assemble(e, f, g, h)), _)}} : Maybe<&2, List<&2, U32>>}
      T.encode_text_measured_and_exact(s, W.assemble(a, b, c, d), W.assemble(e, f, g, h), text_valid, measure_text)

def analyze_header_textual(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +bs: List<&2, U32>,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  header: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool},
  accepted: {C.traverse(B.concatenate([a, b, c, d, e, f, g, h], bs), body, ceiling, C.WordInput{C.TextValue{}, 7n, 0, 0, C.Root{}}) == C.Decoded{v} : C.Outcome}) ->
  ContentDecoded<bs, B.Number64{W.assemble(a, b, c, d), W.assemble(e, f, g, h)}, v>:
  conclude_word_textual_accepts_reconstructs_content(bs, W.assemble(a, b, c, d), W.assemble(e, f, g, h), H.decrease(8n, body), H.decrease(8n, ceiling), v,
    (%W.eight_octets_all_valid_conclude_word(C.TextValue{}, a, b, c, d, e, f, g, h, C.Root{}, body, ceiling, header) :
      {R.traverse_frame(bs, _) == C.Decoded{v} : C.Outcome}
      %R.execution_trace_of_concatenation([a, b, c, d, e, f, g, h], bs, R.Frame{body, ceiling, C.WordInput{C.TextValue{}, 7n, 0, 0, C.Root{}}}) :
        {_ == C.Decoded{v} : C.Outcome}
      accepted))

def text_accepted_header(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +bs: List<&2, U32>,
  +ceiling: B.Number64, -v: D.Value,
  valid: {D.value_valid(v) == True{} : Bool},
  input: R.InputChecked<B.nat64(B.length(Con{4, B.concatenate([a, b, c, d, e, f, g, h], bs)})), Con{4, B.concatenate([a, b, c, d, e, f, g, h], bs)}, ceiling, v>) ->
  P.Encoding(v, Con{4, B.concatenate([a, b, c, d, e, f, g, h], bs)}):
  match input:
    case R.Checked{+body, measure, fits, octets, execution_trace}:
      +header = octets_all_valid_of_prefix([a, b, c, d, e, f, g, h], bs,
        F.and_boolean_right(True{}, B.octets_all_valid(B.concatenate([a, b, c, d, e, f, g, h], bs)), octets))
      reencode_text_combined_header(a, b, c, d, e, f, g, h, bs, v, valid, header,
        analyze_header_textual(a, b, c, d, e, f, g, h, bs, C.decrease64(body), C.decrease64(ceiling), v, header, execution_trace))

# Unlike integers, text may have bytes AFTER the length word.
def WordSufficient(n: Nat, bs: List<&2, U32>) -> Type:
  match n bs:
    case 0n Nil{}:
      Empty
    case 0n Con{b, t}:
      Unit
    case 1n+p Nil{}:
      Empty
    case 1n+p Con{b, t}:
      WordSufficient(p, t)

law word_accepts_requires_all_os_octets_of_header:
  for n: Nat
  for +bs: List<&2, U32>
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.traverse(bs, body, ceiling, C.WordInput{C.TextValue{}, n, high, low, C.Root{}}) == C.Decoded{v} : C.Outcome}
  WordSufficient(n, bs)
def word_accepts_requires_all_os_octets_of_header(n, bs, high, low, body, ceiling, v, accepted):
  match n bs:
    case 0n Nil{}:
      R.input_negative_decoded(v, accepted)
    case 0n Con{b, t}:
      Unit{}
    case 1n+p Nil{}:
      R.input_negative_decoded(v, accepted)
    case 1n+p Con{+b, +t}:
      word_accepts_requires_all_os_octets_of_header(p, t, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), C.decrease64(body), C.decrease64(ceiling), v, accepted)

def text_accepted_combined_format(+bs: List<&2, U32>, +ceiling: B.Number64, -v: D.Value,
  valid: {D.value_valid(v) == True{} : Bool},
  accepted: {C.decode(Con{4, bs}, ceiling) == C.Decoded{v} : C.Outcome},
  format: WordSufficient(7n, bs)) -> P.Encoding(v, Con{4, bs}):
  match bs:
    case Nil{}:
      L.ex_false(P.Encoding(v, Con{4, Nil{}}), format)
    case Con{a0, Nil{}}:
      L.ex_false(P.Encoding(v, Con{4, Con{a0, Nil{}}}), format)
    case Con{a0, Con{a1, Nil{}}}:
      L.ex_false(P.Encoding(v, Con{4, Con{a0, Con{a1, Nil{}}}}), format)
    case Con{a0, Con{a1, Con{a2, Nil{}}}}:
      L.ex_false(P.Encoding(v, Con{4, Con{a0, Con{a1, Con{a2, Nil{}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}:
      L.ex_false(P.Encoding(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}:
      L.ex_false(P.Encoding(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}:
      L.ex_false(P.Encoding(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}:
      L.ex_false(P.Encoding(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}}), format)
    case Con{+a0, Con{+a1, Con{+a2, Con{+a3, Con{+a4, Con{+a5, Con{+a6, Con{+a7, +rest}}}}}}}}:
      text_accepted_header(a0, a1, a2, a3, a4, a5, a6, a7, rest, ceiling, v, valid,
        R.acceptance_requires_body_representable_octets_and_limit(Con{4, B.concatenate([a0, a1, a2, a3, a4, a5, a6, a7], rest)}, ceiling, v, accepted))

def header_textual_accepted_and_complete(+bs: List<&2, U32>, +ceiling: B.Number64, -v: D.Value,
  input: R.InputChecked<B.nat64(B.length(Con{4, bs})), Con{4, bs}, ceiling, v>) -> WordSufficient(7n, bs):
  match input:
    case R.Checked{body, measure, fits, octets, execution_trace}:
      word_accepts_requires_all_os_octets_of_header(7n, bs, 0, 0, C.decrease64(body), C.decrease64(ceiling), v, execution_trace)

law all_acceptance_started_by_tag_text_and_canonical:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for +accepted: {C.decode(Con{4, bs}, ceiling) == C.Decoded{v} : C.Outcome}
  P.Encoding(v, Con{4, bs})
def all_acceptance_started_by_tag_text_and_canonical(bs, ceiling, v, accepted):
  text_accepted_combined_format(bs, ceiling, v, V.decode_only_returns_value_valid(Con{4, bs}, ceiling, v, accepted), accepted,
    header_textual_accepted_and_complete(bs, ceiling, v,
      R.acceptance_requires_body_representable_octets_and_limit(Con{4, bs}, ceiling, v, accepted)))
