# Canonical NAME extraction from actual TagName execution.
# The only public premises are valid bytes and reaching DecodedReady.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O
import ./CodecTrace.bend as R
import ./CodecWordsBE64.bend as H
import ./CodecAcceptanceWord.bend as W
import ./CodecAcceptanceText.bend as T
import ./CodecContent.bend as G
import ./CodecComposition.bend as X
import ./CodecAssembly.bend as M
import ./CodecNamesASCII.bend as A
import ./CodecCanonical.bend as K

def start(stack: C.Stack, body: B.Number64, ceiling: B.Number64) -> R.Frame:
  R.Frame{body, ceiling, C.TagName{stack}}

def content(+q: B.Number64, stack: C.Stack) -> C.Machine:
  C.Content{True{}, C.one64(q), C.decrease64(q), C.Start{}, "", stack}

# On a Name stack, this conclusion reduces the actual comparison with previous.
# Other stacks reject emit_name and admit no accepted continuation.
def OrderName(stack: C.Stack, name: String) -> Type:
  match stack:
    case C.Name{u, q, previous, xs, parent}:
      {String.is_lt(previous, name) == True{} : Bool}
    case _:
      Empty

law emission_name_refused_absorbs_all_suffix:
  for +stack: C.Stack
  for +name: String
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for refused: {C.emit_name(stack, name) == C.Invalid{} : C.Machine}
  {R.machine(R.execute(bs, R.Frame{body, ceiling, C.emit_name(stack, name)})) == C.Invalid{} : C.Machine}
def emission_name_refused_absorbs_all_suffix(stack, name, bs, body, ceiling, refused):
  %Equal.sym(C.Machine, C.emit_name(stack, name), C.Invalid{}, refused) :
    {R.machine(R.execute(bs, R.Frame{body, ceiling, _})) == C.Invalid{} : C.Machine}
  G.execute_invalid_remains_invalid(bs, body, ceiling)

def name_checked_accepted(valid: Bool, +u: Bool, +q: B.Number64,
  +previous: String, +name: String, +xs: List<&2, D.Field>, +parent: C.Stack,
  +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  test: {D.name_valid(name) && String.is_lt(previous, name) == valid : Bool},
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.name_checked(valid, u, q, name, xs, parent)})) == C.DecodedReady{v} : C.Machine}) ->
  L.E<{D.name_valid(name) == True{} : Bool}, {String.is_lt(previous, name) == True{} : Bool}>:
  match valid:
    case False{}:
      T.invalid_negative_terminates_ready(
        L.E<{D.name_valid(name) == True{} : Bool}, {String.is_lt(previous, name) == True{} : Bool}>,
        bs, body, ceiling, v, accepted)
    case True{}:
      F.and_boolean_separate(D.name_valid(name), String.is_lt(previous, name), test)

law continuation_name_accepts_checks_validity_and_order:
  for +stack: C.Stack
  for +name: String
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {R.machine(R.execute(bs,
    R.Frame{body, ceiling, C.emit_name(stack, name)})) == C.DecodedReady{v} : C.Machine}
  L.E<{D.name_valid(name) == True{} : Bool}, OrderName(stack, name)>
def continuation_name_accepts_checks_validity_and_order(stack, name, bs, body, ceiling, v, accepted):
  match stack:
    case C.Name{+u, +q, +previous, +xs, +parent}:
      name_checked_accepted(D.name_valid(name) && String.is_lt(previous, name),
        u, q, previous, name, xs, parent, bs, body, ceiling, v, {==}, accepted)
    case C.Root{}:
      T.invalid_negative_terminates_ready(L.E<{D.name_valid(name) == True{} : Bool}, Empty>,
        bs, body, ceiling, v, accepted)
    case C.ListFrame{u, q, xs, parent}:
      T.invalid_negative_terminates_ready(L.E<{D.name_valid(name) == True{} : Bool}, Empty>,
        bs, body, ceiling, v, accepted)
    case C.Field{u, q, n, xs, parent}:
      T.invalid_negative_terminates_ready(L.E<{D.name_valid(name) == True{} : Bool}, Empty>,
        bs, body, ceiling, v, accepted)

law execute_above_remains_above:
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Above{}})) == C.Above{} : C.Machine}
def execute_above_remains_above(bs, body, ceiling):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      execute_above_remains_above(t, C.decrease64(body), C.decrease64(ceiling))

def above_negative_terminates_ready(-A0: Type, +bs: List<&2, U32>,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Above{}})) == C.DecodedReady{v} : C.Machine}) -> A0:
  L.ex_false(A0, F.false_negative_true(Equal.cong(C.Machine, Bool, m => T.ready(m), C.Above{}, C.DecodedReady{v},
    Equal.trans(C.Machine, C.Above{}, R.machine(R.execute(bs, R.Frame{body, ceiling, C.Above{}})), C.DecodedReady{v},
      Equal.sym(C.Machine, R.machine(R.execute(bs, R.Frame{body, ceiling, C.Above{}})), C.Above{},
        execute_above_remains_above(bs, body, ceiling)), accepted))))

law name_of_size_zero_negative_accepts:
  for +bs: List<&2, U32>
  for +q: B.Number64
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.open_variable(True{}, C.NameText{}, q, stack)})) == C.DecodedReady{v} : C.Machine}
  Empty
def name_of_size_zero_negative_accepts(bs, q, stack, body, ceiling, v, accepted):
  T.invalid_negative_terminates_ready(Empty, bs, body, ceiling, v, accepted)

def open_name_accepted(fits: Bool, +q: B.Number64, +stack: C.Stack,
  +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_name(fits, q, stack)})) == C.DecodedReady{v} : C.Machine}) ->
  {C.open_name(fits, q, stack) == content(q, stack) : C.Machine}:
  match fits:
    case False{}:
      T.invalid_negative_terminates_ready({C.Invalid{} == content(q, stack) : C.Machine}, bs, body, ceiling, v, accepted)
    case True{}:
      {==}

def open_variable_name_accepted(empty: Bool, +q: B.Number64, +stack: C.Stack,
  +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.open_variable(empty, C.NameText{}, q, stack)})) == C.DecodedReady{v} : C.Machine}) ->
  {C.open_variable(empty, C.NameText{}, q, stack) == content(q, stack) : C.Machine}:
  match empty:
    case True{}:
      L.ex_false({C.Invalid{} == content(q, stack) : C.Machine},
        name_of_size_zero_negative_accepts(bs, q, stack, body, ceiling, v, accepted))
    case False{}:
      open_name_accepted(C.less_equal64(q, B.Number64{0, 64}), q, stack, bs, body, ceiling, v, accepted)

def open_checked_name_accepted(conf: C.Check, +q: B.Number64, +stack: C.Stack,
  +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.open_checked(conf, C.NameText{}, q, stack)})) == C.DecodedReady{v} : C.Machine}) ->
  {C.open_checked(conf, C.NameText{}, q, stack) == content(q, stack) : C.Machine}:
  match conf:
    case C.Large{}:
      above_negative_terminates_ready({C.Above{} == content(q, stack) : C.Machine}, bs, body, ceiling, v, accepted)
    case C.Short{}:
      T.invalid_negative_terminates_ready({C.Invalid{} == content(q, stack) : C.Machine}, bs, body, ceiling, v, accepted)
    case C.Fits{}:
      open_variable_name_accepted(C.zero64(q), q, stack, bs, body, ceiling, v, accepted)

law header_name_accepted_opens_content:
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.conclude_word(C.NameText{}, high, low, stack, body, ceiling)})) == C.DecodedReady{v} : C.Machine}
  {C.conclude_word(C.NameText{}, high, low, stack, body, ceiling) == content(B.Number64{high, low}, stack) : C.Machine}
def header_name_accepted_opens_content(high, low, stack, bs, body, ceiling, v, accepted):
  open_checked_name_accepted(C.check(
    C.sum_optional(C.minimum_field(C.NameText{}, B.Number64{high, low}), C.minimum_stack(stack)), body, ceiling),
    B.Number64{high, low}, stack, bs, body, ceiling, v, accepted)

# bytes_name is a prefix of the ORIGINAL input. Its BE64 header and
# UTF-8 measure are conclusions of the two inversions, not hypotheses.
type NameExtracted<-bs: List<&2, U32>, -body: B.Number64, -ceiling: B.Number64,
  -stack: C.Stack, -v: D.Value> is Type:
  NameExtracted{bytes_name: List<&2, U32>, name: String, suffix: List<&2, U32>,
    high: U32, low: U32, utf8: List<&2, U32>,
    body_emission: B.Number64, ceiling_emission: B.Number64,
    header: {bytes_name == M.prefix(4, B.Number64{high, low}, utf8) : List<&2, U32>},
    factoring: {bs == B.concatenate(bytes_name, suffix) : List<&2, U32>},
    octets_name: {B.octets_all_valid(bytes_name) == True{} : Bool},
    rest_valid: {B.octets_all_valid(suffix) == True{} : Bool},
    positive: G.NotEmpty(utf8),
    bytes: {B.utf8(name) == utf8 : List<&2, U32>},
    measure: {B.nat64(B.length(utf8)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>},
    valid: {D.name_valid(name) == True{} : Bool},
    order: OrderName(stack, name),
    canonical: {P.text(name) == Some{bytes_name} : Maybe<&2, List<&2, U32>>},
    body_exact: {body_emission == H.decrease(B.length(bytes_name), body) : B.Number64},
    ceiling_exact: {ceiling_emission == H.decrease(B.length(bytes_name), ceiling) : B.Number64},
    emission: {R.execute(bytes_name, start(stack, body, ceiling)) ==
      R.Frame{body_emission, ceiling_emission, C.emit_name(stack, name)} : R.Frame},
    execution: {R.execute(suffix, R.Frame{body_emission, ceiling_emission, C.emit_name(stack, name)}) ==
      R.execute(bs, start(stack, body, ceiling)) : R.Frame},
    continuation: {R.machine(R.execute(suffix,
      R.Frame{body_emission, ceiling_emission, C.emit_name(stack, name)})) == C.DecodedReady{v} : C.Machine}}

def body_frame(q: R.Frame) -> B.Number64:
  R.Frame{c, t, m} = q
  c

def ceiling_frame(q: R.Frame) -> B.Number64:
  R.Frame{c, t, m} = q
  t

def execution_after_prefix(+bs: List<&2, U32>, +prefix: List<&2, U32>, +suffix: List<&2, U32>,
  +start0: R.Frame, +end: R.Frame,
  division: {bs == B.concatenate(prefix, suffix) : List<&2, U32>},
  emission: {R.execute(prefix, start0) == end : R.Frame}) ->
  {R.execute(suffix, end) == R.execute(bs, start0) : R.Frame}:
  Equal.sym(R.Frame, R.execute(bs, start0), R.execute(suffix, end),
    Equal.trans(R.Frame, R.execute(bs, start0), R.execute(B.concatenate(prefix, suffix), start0), R.execute(suffix, end),
      Equal.cong(List<&2, U32>, R.Frame, xs => R.execute(xs, start0), bs, B.concatenate(prefix, suffix), division),
      Equal.trans(R.Frame, R.execute(B.concatenate(prefix, suffix), start0),
        R.execute(suffix, R.execute(prefix, start0)), R.execute(suffix, end),
        R.execution_of_concatenation(prefix, suffix, start0),
        Equal.cong(R.Frame, R.Frame, q => R.execute(suffix, q), R.execute(prefix, start0), end, emission))))

# Packages facts already extracted; validity and order are obtained only
# NOW, from the accepted continuation of emit_name.
def conclude_name_extracted(+bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +stack: C.Stack, -v: D.Value, +high: U32, +low: U32,
  +utf8: List<&2, U32>, +name: String, +suffix: List<&2, U32>,
  +ca: B.Number64, +ta: B.Number64,
  +division: {bs == B.concatenate(M.prefix(4, B.Number64{high, low}, utf8), suffix) : List<&2, U32>},
  positive: G.NotEmpty(utf8),
  +bytes: {B.utf8(name) == utf8 : List<&2, U32>},
  +measure: {B.nat64(B.length(utf8)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>},
  all_valid: {B.octets_all_valid(bs) == True{} : Bool},
  +emission: {R.execute(M.prefix(4, B.Number64{high, low}, utf8), start(stack, body, ceiling)) ==
    R.Frame{ca, ta, C.emit_name(stack, name)} : R.Frame},
  +accepted: {R.machine(R.execute(suffix,
    R.Frame{ca, ta, C.emit_name(stack, name)})) == C.DecodedReady{v} : C.Machine}) ->
  NameExtracted<bs, body, ceiling, stack, v>:
  +prefix = M.prefix(4, B.Number64{high, low}, utf8)
  +end = {R.Frame{ca, ta, C.emit_name(stack, name)} : R.Frame}
  +counters = Equal.trans(R.Frame, end, R.execute(prefix, start(stack, body, ceiling)),
    X.later(prefix, body, ceiling, C.emit_name(stack, name)),
    Equal.sym(R.Frame, R.execute(prefix, start(stack, body, ceiling)), end, emission),
    X.execution_combined_machine_known_has_counters_exact(prefix, body, ceiling, C.TagName{stack},
      C.emit_name(stack, name), Equal.cong(R.Frame, C.Machine, q => R.machine(q),
        R.execute(prefix, start(stack, body, ceiling)), end, emission)))
  F.combined_pair(NameExtracted<bs, body, ceiling, stack, v>,
    {B.octets_all_valid(prefix) == True{} : Bool}, {B.octets_all_valid(suffix) == True{} : Bool},
    W.separate_octets_all_valid(prefix, suffix,
      (%division :
        {B.octets_all_valid(_) == True{} : Bool}
        all_valid)),
    octets_name => rest_valid =>
      F.combined_pair(NameExtracted<bs, body, ceiling, stack, v>,
        {D.name_valid(name) == True{} : Bool}, OrderName(stack, name),
        continuation_name_accepts_checks_validity_and_order(stack, name, suffix, ca, ta, v, accepted),
        +valid => order =>
          NameExtracted{prefix, name, suffix, high, low, utf8, ca, ta, {==}, division,
            octets_name, rest_valid, positive, bytes, measure, valid, order,
            M.name_measured_has_encoding_textual_exact(name, utf8, B.Number64{high, low},
              A.name_valid_and_text_valid(name, valid), bytes, measure),
            Equal.cong(R.Frame, B.Number64, q => body_frame(q), end,
              X.later(prefix, body, ceiling, C.emit_name(stack, name)), counters),
            Equal.cong(R.Frame, B.Number64, q => ceiling_frame(q), end,
              X.later(prefix, body, ceiling, C.emit_name(stack, name)), counters),
            emission, execution_after_prefix(bs, prefix, suffix, start(stack, body, ceiling), end, division, emission), accepted}))

def assemble_name_textual(+bs: List<&2, U32>, +rest: List<&2, U32>,
  +high: U32, +low: U32, +stack: C.Stack, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  all_valid: {B.octets_all_valid(bs) == True{} : Bool},
  division_header: {bs == Con{4, B.concatenate(B.be64(high, low), rest)} : List<&2, U32>},
  header: {R.execute(Con{4, B.be64(high, low)}, start(stack, body, ceiling)) ==
    R.Frame{H.decrease(8n, C.decrease64(body)), H.decrease(8n, C.decrease64(ceiling)),
      content(B.Number64{high, low}, stack)} : R.Frame},
  extracted: T.ContentCountedAccepted<rest, H.decrease(8n, C.decrease64(body)),
    H.decrease(8n, C.decrease64(ceiling)), True{}, B.Number64{high, low}, stack, v>) ->
  NameExtracted<bs, body, ceiling, stack, v>:
  match extracted:
    case T.ContentCountedAccepted{+utf8, +suffix, +name, +ca, +ta,
      division_text, positive, +bytes, +measure, transduction, emission_text, continuation}:
      +prefix = M.prefix(4, B.Number64{high, low}, utf8)
      +cab = {Con{4, B.be64(high, low)} : List<&2, U32>}
      +c9 = H.decrease(8n, C.decrease64(body))
      +t9 = H.decrease(8n, C.decrease64(ceiling))
      division = Equal.trans(List<&2, U32>, bs, B.concatenate(cab, rest), B.concatenate(prefix, suffix),
        division_header,
        Equal.trans(List<&2, U32>, B.concatenate(cab, rest), B.concatenate(cab, B.concatenate(utf8, suffix)),
          B.concatenate(prefix, suffix),
          Equal.cong(List<&2, U32>, List<&2, U32>, xs => B.concatenate(cab, xs),
            rest, B.concatenate(utf8, suffix), division_text),
          Equal.sym(List<&2, U32>, B.concatenate(prefix, suffix), B.concatenate(cab, B.concatenate(utf8, suffix)),
            K.concatenation_associative(cab, utf8, suffix))))
      emission = Equal.trans(R.Frame, R.execute(prefix, start(stack, body, ceiling)),
        R.execute(utf8, R.execute(cab, start(stack, body, ceiling))), R.Frame{ca, ta, C.emit_name(stack, name)},
        R.execution_of_concatenation(cab, utf8, start(stack, body, ceiling)),
        Equal.trans(R.Frame, R.execute(utf8, R.execute(cab, start(stack, body, ceiling))),
          R.execute(utf8, R.Frame{c9, t9, content(B.Number64{high, low}, stack)}),
          R.Frame{ca, ta, C.emit_name(stack, name)},
          Equal.cong(R.Frame, R.Frame, q => R.execute(utf8, q), R.execute(cab, start(stack, body, ceiling)),
            R.Frame{c9, t9, content(B.Number64{high, low}, stack)}, header), emission_text))
      conclude_name_extracted(bs, body, ceiling, stack, v, high, low, utf8, name, suffix, ca, ta,
        division, positive, bytes, measure, all_valid, emission, continuation)

def assemble_name_word(+bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +stack: C.Stack, -v: D.Value,
  all_valid: {B.octets_all_valid(Con{4, bs}) == True{} : Bool},
  word: W.WordExtracted<bs, C.NameText{}, stack, C.decrease64(body), C.decrease64(ceiling), v>) ->
  NameExtracted<Con{4, bs}, body, ceiling, stack, v>:
  match word:
    case W.Extracted{+a, +b, +c, +d, +e, +f0, +g, +h, +rest, +high, +low,
      factoring, octets, rest_valid, number, +be64, factoring_be64, frame, execution, +ready}:
      +c9 = H.decrease(8n, C.decrease64(body))
      +t9 = H.decrease(8n, C.decrease64(ceiling))
      +opening = header_name_accepted_opens_content(high, low, stack, rest, c9, t9, v, ready)
      header = Equal.trans(R.Frame,
        R.execute(Con{4, B.be64(high, low)}, start(stack, body, ceiling)),
        W.after_word(C.NameText{}, high, low, stack, C.decrease64(body), C.decrease64(ceiling)),
        R.Frame{c9, t9, content(B.Number64{high, low}, stack)},
        (%Equal.sym(List<&2, U32>, B.be64(high, low), [a, b, c, d, e, f0, g, h], be64) :
          {R.execute(_, W.start(C.NameText{}, stack, C.decrease64(body), C.decrease64(ceiling))) ==
          W.after_word(C.NameText{}, high, low, stack, C.decrease64(body), C.decrease64(ceiling)) : R.Frame}
          frame),
        Equal.cong(C.Machine, R.Frame, m => R.Frame{c9, t9, m},
          C.conclude_word(C.NameText{}, high, low, stack, c9, t9),
          content(B.Number64{high, low}, stack), opening))
      assemble_name_textual(Con{4, bs}, rest, high, low, stack, body, ceiling, v, all_valid,
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{4, xs}, bs, B.concatenate(B.be64(high, low), rest), factoring_be64),
        header,
        T.content_counted_accepted_reconstructs_prefix_text_and_count(rest, c9, t9, True{}, B.Number64{high, low}, stack, v,
          (%opening :
            {R.machine(R.execute(rest, R.Frame{c9, t9, _})) == C.DecodedReady{v} : C.Machine}
            ready)))

def read_tag_name_accepts(correct: Bool, +stack: C.Stack, +bs: List<&2, U32>,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.read_tag_name(correct, stack)})) == C.DecodedReady{v} : C.Machine}) ->
  {correct == True{} : Bool}:
  match correct:
    case False{}:
      T.invalid_negative_terminates_ready({False{} == True{} : Bool}, bs, body, ceiling, v, accepted)
    case True{}:
      {==}

# The tag is an arbitrary received U32. Its equality to 4 follows from
# acceptance of read_tag_name(U32.is_eq(tag,4)), before inverting the word.
law tag_name_accepts_extracts_prefix_canonical:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +stack: C.Stack
  for -v: D.Value
  for +all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for +accepted: {R.machine(R.execute(bs, start(stack, body, ceiling))) == C.DecodedReady{v} : C.Machine}
  NameExtracted<bs, body, ceiling, stack, v>
def tag_name_accepts_extracts_prefix_canonical(bs, body, ceiling, stack, v, all_valid, accepted):
  match bs:
    case Nil{}:
      L.ex_false(NameExtracted<Nil{}, body, ceiling, stack, v>,
        F.false_negative_true(Equal.cong(C.Machine, Bool, m => T.ready(m), C.TagName{stack}, C.DecodedReady{v}, accepted)))
    case Con{+tag, +tail}:
      +tag4 = O.u32_equal(tag, 4, O.cmp_eq(U32.cmp(tag, 4),
        read_tag_name_accepts(U32.is_eq(tag, 4), stack, tail, C.decrease64(body), C.decrease64(ceiling), v, accepted)))
      %Equal.sym(U32, tag, 4, tag4) : NameExtracted<Con{_, tail}, body, ceiling, stack, v>
      assemble_name_word(tail, body, ceiling, stack, v,
        (%tag4 : {B.octets_all_valid(Con{_, tail}) == True{} : Bool}
          all_valid),
        W.word_accepts_extracts_be64_and_execution_remaining(tail, C.NameText{}, stack,
          C.decrease64(body), C.decrease64(ceiling), v,
          F.and_boolean_right(U32.is_le(tag, 255), B.octets_all_valid(tail), all_valid),
          (%tag4 :
            {R.machine(R.execute(Con{_, tail}, start(stack, body, ceiling))) == C.DecodedReady{v} : C.Machine}
            accepted)))

# Specialization for the exact instant requested by the record step.
# OrderName reduces here to String.is_lt(previous,name)==True.
law name_accepted_extracts_prefix_canonical:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +u: Bool
  for +q: B.Number64
  for +previous: String
  for +xs: List<&2, D.Field>
  for +parent: C.Stack
  for -v: D.Value
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for accepted: {R.machine(R.execute(bs,
    R.Frame{body, ceiling, C.TagName{C.Name{u, q, previous, xs, parent}}})) == C.DecodedReady{v} : C.Machine}
  NameExtracted<bs, body, ceiling, C.Name{u, q, previous, xs, parent}, v>
def name_accepted_extracts_prefix_canonical(bs, body, ceiling, u, q, previous, xs, parent, v, all_valid, accepted):
  tag_name_accepts_extracts_prefix_canonical(bs, body, ceiling, C.Name{u, q, previous, xs, parent}, v, all_valid, accepted)
