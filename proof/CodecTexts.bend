# General text composition: transduction -> actual Content -> public API.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecUTF8.bend as U
import ./CodecUTF8Inverse.bend as V
import ./CodecContent.bend as G
import ./CodecCounters.bend as N
import ./CodecMinimum.bend as M
import ./CodecWordsBE64.bend as H
import ./CodecTrace.bend as R
import ./CodecIntegers.bend as J
import ./CodecUTF8InverseOctets.bend as O
import ./CodecUnicode.bend as Q
import ./CodecCanonical.bend as K
import ../contract/Protocol.bend as P

def conclude_transduction_accepts(+name: Bool, +stack: C.Stack,
  +t: U.TextValue, -s: String,
  accepted: {U.finalize_text(t) == Some{s} : Maybe<&2, String>}) ->
  {G.conclude_text(name, stack, t) == C.emit_text(name, s, stack) : C.Machine}:
  match t:
    case U.TextInvalid{}:
      L.ex_false({C.Invalid{} == C.emit_text(name, s, stack) : C.Machine}, F.none_negative_some(String, s, accepted))
    case U.Reading{C.Start{}, +inverted}:
      Equal.cong(String, C.Machine, text => C.emit_text(name, text, stack), String.reverse(inverted), s,
        F.some_injective(String, String.reverse(inverted), s, accepted))
    case U.Reading{C.Continue{n, cp, minimum}, inverted}:
      L.ex_false({C.Invalid{} == C.emit_text(name, s, stack) : C.Machine}, F.none_negative_some(String, s, accepted))

law opening_textual_counted_reproduces_transduction_accepts:
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for -s: String
  for +measured: {B.nat64(B.length(bs)) == Some{q} : Maybe<&2, B.Number64>}
  for accepted: {U.finalize_text(U.traverse_text(bs, U.Reading{C.Start{}, ""})) == Some{s} : Maybe<&2, String>}
  {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.TextValue{}, q, C.Root{})})) == C.DecodedReady{D.VText{s}} : C.Machine}
def opening_textual_counted_reproduces_transduction_accepts(bs, q, body, ceiling, s, measured, accepted):
  match bs:
    case Nil{}:
      %F.some_injective(B.Number64, B.Number64{0, 0}, q, measured) :
        {R.machine(R.execute(Nil{}, R.Frame{body, ceiling, C.open_variable(C.zero64(_), C.TextValue{}, q, C.Root{})})) == C.DecodedReady{D.VText{s}} : C.Machine}
      Equal.cong(String, C.Machine, text => C.DecodedReady{D.VText{text}}, "", s, F.some_injective(String, "", s, accepted))
    case Con{+b, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflects_count_natural(B.length(Con{b, t}), q, measured)) :
        {R.machine(R.execute(Con{b, t}, R.Frame{body, ceiling, C.open_variable(_, C.TextValue{}, q, C.Root{})})) == C.DecodedReady{D.VText{s}} : C.Machine}
      Equal.trans(C.Machine,
        G.process_content(Con{b, t}, q, body, ceiling, False{}, C.Start{}, "", C.Root{}),
        G.conclude_text(False{}, C.Root{}, U.traverse_text(Con{b, t}, U.Reading{C.Start{}, ""})), C.DecodedReady{D.VText{s}},
        G.content_counted_consume_exactly_o_text(Con{b, t}, q, body, ceiling, False{}, C.Start{}, "", C.Root{}, Unit{}, measured),
        conclude_transduction_accepts(False{}, C.Root{}, U.traverse_text(Con{b, t}, U.Reading{C.Start{}, ""}), s, accepted))

law text_canonical_counted_and_reproduced_exactly:
  for +s: String
  for +q: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for valid: {B.text_valid(s) == True{} : Bool}
  for +measured: {B.nat64(B.length(B.utf8(s))) == Some{q} : Maybe<&2, B.Number64>}
  {R.machine(R.execute(B.utf8(s), R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.TextValue{}, q, C.Root{})})) == C.DecodedReady{D.VText{s}} : C.Machine}
def text_canonical_counted_and_reproduced_exactly(s, q, body, ceiling, valid, measured):
  opening_textual_counted_reproduces_transduction_accepts(B.utf8(s), q, body, ceiling, s, measured, V.utf8_text_valid_decodes_exactly(s, valid))

law decrease_commutes_combined_iteration:
  for +n: Nat
  for +q: B.Number64
  {H.decrease(n, C.decrease64(q)) == C.decrease64(H.decrease(n, q)) : B.Number64}
def decrease_commutes_combined_iteration(n, q):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(B.Number64, B.Number64, x => C.decrease64(x), H.decrease(p, C.decrease64(q)), C.decrease64(H.decrease(p, q)), decrease_commutes_combined_iteration(p, q))

law remove_prefix_of_measure:
  for +n: Nat
  for +rest: Nat
  for +body: B.Number64
  for measured: {B.nat64(Nat.add(n, rest)) == Some{body} : Maybe<&2, B.Number64>}
  {B.nat64(rest) == Some{H.decrease(n, body)} : Maybe<&2, B.Number64>}
def remove_prefix_of_measure(n, rest, body, measured):
  match n:
    case 0n:
      measured
    case 1n+p:
      %decrease_commutes_combined_iteration(p, body) :
        {B.nat64(rest) == Some{_} : Maybe<&2, B.Number64>}
      remove_prefix_of_measure(p, rest, C.decrease64(body),
        N.measure_decremented(Nat.add(p, rest), body, N.nat64_successor_has_predecessor_exact(Nat.add(p, rest), body, measured)))

law conclude_text_in_root_checks_o_minimum_exact:
  for +high: U32
  for +low: U32
  for +ceiling: B.Number64
  for fits: {C.less_equal64(B.Number64{high, low}, ceiling) == True{} : Bool}
  {C.conclude_word(C.TextValue{}, high, low, C.Root{}, B.Number64{high, low}, ceiling) ==
    C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{}) : C.Machine}
def conclude_text_in_root_checks_o_minimum_exact(high, low, ceiling, fits):
  %Equal.sym(Maybe<&2, B.Number64>, C.sum_optional(C.minimum_field(C.TextValue{}, B.Number64{high, low}), C.minimum_stack(C.Root{})), Some{B.Number64{high, low}},
    M.minimum_textual_in_root_and_exactly_to_count(B.Number64{high, low})) :
    {C.open_checked(C.check(_, B.Number64{high, low}, ceiling), C.TextValue{}, B.Number64{high, low}, C.Root{}) == C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{}) : C.Machine}
  %Equal.sym(C.Check, C.check(Some{B.Number64{high, low}}, B.Number64{high, low}, ceiling), C.Fits{},
    M.check_minimum_equal_to_body_allows_limit(B.Number64{high, low}, ceiling, fits)) :
    {C.open_checked(_, C.TextValue{}, B.Number64{high, low}, C.Root{}) == C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{}) : C.Machine}
  {==}

def bytes_text(high: U32, low: U32, s: String) -> List<&2, U32>:
  Con{4, B.concatenate(B.be64(high, low), B.utf8(s))}

law header_textual_canonical_opens_exactly_o_content:
  for +s: String
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for measure_text: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for measure_body: {B.nat64(B.length(bytes_text(high, low, s))) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.execute(Con{4, B.be64(high, low)}, R.Frame{body, ceiling, C.Tag{C.Root{}}}) ==
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{})} : R.Frame}
def header_textual_canonical_opens_exactly_o_content(s, high, low, body, ceiling, measure_text, measure_body, fits):
  measure_rest = remove_prefix_of_measure(9n, B.length(B.utf8(s)), body, measure_body)
  +rest_equal = F.some_injective(B.Number64, H.decrease(9n, body), B.Number64{high, low},
    Equal.trans(Maybe<&2, B.Number64>, Some{H.decrease(9n, body)}, B.nat64(B.length(B.utf8(s))), Some{B.Number64{high, low}},
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(B.utf8(s))), Some{H.decrease(9n, body)}, measure_rest), measure_text))
  fits_rest = {(%rest_equal : {C.less_equal64(_, H.decrease(9n, ceiling)) == True{} : Bool}
    M.decrease_repeated_preserves_order_of_limits(9n, body, ceiling, fits)) : {C.less_equal64(B.Number64{high, low}, H.decrease(9n, ceiling)) == True{} : Bool}}
  conclude = {(%Equal.sym(B.Number64, H.decrease(9n, body), B.Number64{high, low}, rest_equal) :
    {C.conclude_word(C.TextValue{}, high, low, C.Root{}, _, H.decrease(9n, ceiling)) ==
      C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{}) : C.Machine}
    conclude_text_in_root_checks_o_minimum_exact(high, low, H.decrease(9n, ceiling), fits_rest)) :
    {C.conclude_word(C.TextValue{}, high, low, C.Root{}, H.decrease(9n, body), H.decrease(9n, ceiling)) == C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{}) : C.Machine}}
  Equal.trans(R.Frame,
    R.execute(Con{4, B.be64(high, low)}, R.Frame{body, ceiling, C.Tag{C.Root{}}}),
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.conclude_word(C.TextValue{}, high, low, C.Root{}, H.decrease(9n, body), H.decrease(9n, ceiling))},
    R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{})},
    H.be64_concludes_word(C.TextValue{}, high, low, C.Root{}, C.decrease64(body), C.decrease64(ceiling)),
    Equal.cong(C.Machine, R.Frame, m => R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), m},
      C.conclude_word(C.TextValue{}, high, low, C.Root{}, H.decrease(9n, body), H.decrease(9n, ceiling)),
      C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{}), conclude))

law execute_text_canonical_inside_of_limit_and_exact:
  for +s: String
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for valid: {B.text_valid(s) == True{} : Bool}
  for +measure_text: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for measure_body: {B.nat64(B.length(bytes_text(high, low, s))) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {R.machine(R.execute(bytes_text(high, low, s), R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{D.VText{s}} : C.Machine}
def execute_text_canonical_inside_of_limit_and_exact(s, high, low, body, ceiling, valid, measure_text, measure_body, fits):
  header = header_textual_canonical_opens_exactly_o_content(s, high, low, body, ceiling, measure_text, measure_body, fits)
  Equal.trans(C.Machine,
    R.machine(R.execute(bytes_text(high, low, s), R.Frame{body, ceiling, C.Tag{C.Root{}}})),
    R.machine(R.execute(B.utf8(s), R.execute(Con{4, B.be64(high, low)}, R.Frame{body, ceiling, C.Tag{C.Root{}}}))),
    C.DecodedReady{D.VText{s}},
    Equal.cong(R.Frame, C.Machine, q => R.machine(q),
      R.execute(bytes_text(high, low, s), R.Frame{body, ceiling, C.Tag{C.Root{}}}),
      R.execute(B.utf8(s), R.execute(Con{4, B.be64(high, low)}, R.Frame{body, ceiling, C.Tag{C.Root{}}})),
      R.execution_of_concatenation(Con{4, B.be64(high, low)}, B.utf8(s), R.Frame{body, ceiling, C.Tag{C.Root{}}})),
    Equal.trans(C.Machine,
      R.machine(R.execute(B.utf8(s), R.execute(Con{4, B.be64(high, low)}, R.Frame{body, ceiling, C.Tag{C.Root{}}}))),
      R.machine(R.execute(B.utf8(s), R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{})})),
      C.DecodedReady{D.VText{s}},
      Equal.cong(R.Frame, C.Machine, q => R.machine(R.execute(B.utf8(s), q)),
        R.execute(Con{4, B.be64(high, low)}, R.Frame{body, ceiling, C.Tag{C.Root{}}}),
        R.Frame{H.decrease(9n, body), H.decrease(9n, ceiling), C.open_variable(C.zero64(B.Number64{high, low}), C.TextValue{}, B.Number64{high, low}, C.Root{})}, header),
      text_canonical_counted_and_reproduced_exactly(s, B.Number64{high, low}, H.decrease(9n, body), H.decrease(9n, ceiling), valid, measure_text)))

law all_text_canonical_inside_of_limit_and_accepted:
  for +s: String
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for +valid: {B.text_valid(s) == True{} : Bool}
  for +measure_text: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  for +measure_body: {B.nat64(B.length(bytes_text(high, low, s))) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.decode(bytes_text(high, low, s), ceiling) == C.Decoded{D.VText{s}} : C.Outcome}
def all_text_canonical_inside_of_limit_and_accepted(s, high, low, body, ceiling, valid, measure_text, measure_body, fits):
  octets = J.concatenate_preserves_octets(B.be64(high, low), B.utf8(s), J.be64_only_emits_octets(high, low), O.utf8_text_valid_emits_octets(s, valid))
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bytes_text(high, low, s))), Some{body}, measure_body) :
    {C.decode_measure(_, bytes_text(high, low, s), ceiling) == C.Decoded{D.VText{s}} : C.Outcome}
  %Equal.sym(Bool, C.less_equal64(body, ceiling), True{}, fits) :
    {C.decode_size(_, bytes_text(high, low, s), body, ceiling) == C.Decoded{D.VText{s}} : C.Outcome}
  %Equal.sym(Bool, B.octets_all_valid(bytes_text(high, low, s)), True{}, octets) :
    {C.decode_octets(_, bytes_text(high, low, s), body, ceiling) == C.Decoded{D.VText{s}} : C.Outcome}
  Equal.trans(C.Outcome, C.traverse(bytes_text(high, low, s), body, ceiling, C.Tag{C.Root{}}),
    R.finalize_frame(R.execute(bytes_text(high, low, s), R.Frame{body, ceiling, C.Tag{C.Root{}}})), C.Decoded{D.VText{s}},
    R.execution_trace_and_execution_integral(bytes_text(high, low, s), R.Frame{body, ceiling, C.Tag{C.Root{}}}),
    Equal.cong(C.Machine, C.Outcome, m => C.finalize(m), R.machine(R.execute(bytes_text(high, low, s), R.Frame{body, ceiling, C.Tag{C.Root{}}})), C.DecodedReady{D.VText{s}},
      execute_text_canonical_inside_of_limit_and_exact(s, high, low, body, ceiling, valid, measure_text, measure_body, fits)))

law predicates_of_text_agree:
  for +s: String
  {B.text_valid(s) == D.unicode_valid(s) : Bool}
def predicates_of_text_agree(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      %Equal.sym(Bool, B.code_valid(cp), D.scalar_valid(cp), Q.predicates_unicode_agree(cp)) :
        {_ && B.text_valid(t) == D.scalar_valid(cp) && D.unicode_valid(t) : Bool}
      Equal.cong(Bool, Bool, b => D.scalar_valid(cp) && b, B.text_valid(t), D.unicode_valid(t), predicates_of_text_agree(t))

law finalize_atom_optional_preserves_result:
  for m: Maybe<&2, List<&2, U32>>
  {P.finalize(P.atom_optional(m)) == m : Maybe<&2, List<&2, U32>>}
def finalize_atom_optional_preserves_result(m):
  match m:
    case None{}:
      {==}
    case Some{bs}:
      {==}

law encoding_requires_value_valid:
  for valid: Bool
  for -result: Maybe<&2, List<&2, U32>>
  for -bs: List<&2, U32>
  for accepted: {P.encode_cases(valid, result) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {valid == True{} : Bool}
def encoding_requires_value_valid(valid, result, bs, accepted):
  match valid:
    case False{}:
      L.ex_false({False{} == True{} : Bool}, F.none_negative_some(List<&2, U32>, bs, accepted))
    case True{}:
      {==}

type TextEncoded<-s: String, -bs: List<&2, U32>> is Type:
  TextEncoded{high: U32, low: U32,
    valid: {B.text_valid(s) == True{} : Bool},
    measure: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>},
    bytes: {bytes_text(high, low, s) == bs : List<&2, U32>}}

def size_textual_encoded(n: Maybe<&2, B.Number64>, +s: String, -bs: List<&2, U32>,
  valid: {B.text_valid(s) == True{} : Bool},
  measure: {B.nat64(B.length(B.utf8(s))) == n : Maybe<&2, B.Number64>},
  encoded: {P.prefix_size(4, B.number64_bytes(n), B.utf8(s)) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> TextEncoded<s, bs>:
  match n:
    case None{}:
      L.ex_false(TextEncoded<s, bs>, F.none_negative_some(List<&2, U32>, bs, encoded))
    case Some{B.Number64{+high, +low}}:
      TextEncoded{high, low, valid, measure, F.some_injective(List<&2, U32>, bytes_text(high, low, s), bs, encoded)}

law encoding_of_text_exposes_text_measure_and_bytes_exact:
  for +s: String
  for -bs: List<&2, U32>
  for +encoded: {P.encode(D.VText{s}) == Some{bs} : Maybe<&2, List<&2, U32>>}
  TextEncoded<s, bs>
def encoding_of_text_exposes_text_measure_and_bytes_exact(s, bs, encoded):
  +unicode = encoding_requires_value_valid(D.unicode_valid(s), P.finalize(P.encode_partial(D.VText{s})), bs, encoded)
  +valid = Equal.trans(Bool, B.text_valid(s), D.unicode_valid(s), True{}, predicates_of_text_agree(s), unicode)
  text = Equal.trans(Maybe<&2, List<&2, U32>>, P.text(s), P.encode(D.VText{s}), Some{bs},
    Equal.trans(Maybe<&2, List<&2, U32>>, P.text(s), P.finalize(P.atom_optional(P.text(s))), P.encode(D.VText{s}),
      Equal.sym(Maybe<&2, List<&2, U32>>, P.finalize(P.atom_optional(P.text(s))), P.text(s), finalize_atom_optional_preserves_result(P.text(s))),
      Equal.sym(Maybe<&2, List<&2, U32>>, P.encode(D.VText{s}), P.finalize(P.encode_partial(D.VText{s})), K.value_valid_releases_encoding(D.VText{s}, unicode))), encoded)
  size_textual_encoded(B.nat64(B.length(B.utf8(s))), s, bs, valid, {==},
    (%valid : {P.text_cases(_, B.utf8(s)) == Some{bs} : Maybe<&2, List<&2, U32>>}
      text))

def accept_text_encoded(+s: String, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  measure_body: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(body, ceiling) == True{} : Bool},
  data: TextEncoded<s, bs>) -> {C.decode(bs, ceiling) == C.Decoded{D.VText{s}} : C.Outcome}:
  match data:
    case TextEncoded{+high, +low, valid, measure, +bytes}:
      %bytes : {C.decode(_, ceiling) == C.Decoded{D.VText{s}} : C.Outcome}
      all_text_canonical_inside_of_limit_and_accepted(s, high, low, body, ceiling, valid, measure,
        (%Equal.sym(List<&2, U32>, bytes_text(high, low, s), bs, bytes) :
          {B.nat64(B.length(_)) == Some{body} : Maybe<&2, B.Number64>}
          measure_body), fits)

law all_encoding_textual_inside_of_limit_and_accepts:
  for +s: String
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +encoded: {P.encode(D.VText{s}) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for measure_body: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.decode(bs, ceiling) == C.Decoded{D.VText{s}} : C.Outcome}
def all_encoding_textual_inside_of_limit_and_accepts(s, bs, body, ceiling, encoded, measure_body, fits):
  accept_text_encoded(s, bs, body, ceiling, measure_body, fits, encoding_of_text_exposes_text_measure_and_bytes_exact(s, bs, encoded))

law encode_text_measured_and_exact:
  for +s: String
  for +high: U32
  for +low: U32
  for +valid: {B.text_valid(s) == True{} : Bool}
  for measure: {B.nat64(B.length(B.utf8(s))) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {P.encode(D.VText{s}) == Some{bytes_text(high, low, s)} : Maybe<&2, List<&2, U32>>}
def encode_text_measured_and_exact(s, high, low, valid, measure):
  unicode = Equal.trans(Bool, D.unicode_valid(s), B.text_valid(s), True{}, Equal.sym(Bool, B.text_valid(s), D.unicode_valid(s), predicates_of_text_agree(s)), valid)
  Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(D.VText{s}), P.text(s), Some{bytes_text(high, low, s)},
    Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(D.VText{s}), P.finalize(P.atom_optional(P.text(s))), P.text(s),
      K.value_valid_releases_encoding(D.VText{s}, unicode), finalize_atom_optional_preserves_result(P.text(s))),
    (%Equal.sym(Bool, B.text_valid(s), True{}, valid) : {P.text_cases(_, B.utf8(s)) == Some{bytes_text(high, low, s)} : Maybe<&2, List<&2, U32>>}
      %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(B.utf8(s))), Some{B.Number64{high, low}}, measure) :
        {P.prefix_size(4, B.number64_bytes(_), B.utf8(s)) == Some{bytes_text(high, low, s)} : Maybe<&2, List<&2, U32>>}
      {==}))
