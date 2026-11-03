# Extract the first actual Content emission, before executing the suffix.
# The stack is arbitrary: emit_text may close several ancestors.
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

def ready(m: C.Machine) -> Bool:
  match m:
    case C.DecodedReady{v}:
      True{}
    case _:
      False{}

def invalid_negative_terminates_ready(-A: Type, +bs: List<&2, U32>,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Invalid{}})) == C.DecodedReady{v} : C.Machine}) -> A:
  L.ex_false(A, F.false_negative_true(Equal.cong(C.Machine, Bool, m => ready(m), C.Invalid{}, C.DecodedReady{v},
    Equal.trans(C.Machine, C.Invalid{}, R.machine(R.execute(bs, R.Frame{body, ceiling, C.Invalid{}})), C.DecodedReady{v},
      Equal.sym(C.Machine, R.machine(R.execute(bs, R.Frame{body, ceiling, C.Invalid{}})), C.Invalid{},
        G.execute_invalid_remains_invalid(bs, body, ceiling)), accepted))))

# n counts bytes BEFORE the emitting byte. The last-byte test
# follows from execution, even for an unnormalized initial state.
def last_before(n: Nat, last: Bool, +q: B.Number64) -> Bool:
  match n:
    case 0n:
      last
    case 1n+p:
      Bool.not(last) && last_before(p, C.one64(q), C.decrease64(q))

law last_before_reconstitute_o_protocol_counted:
  for n: Nat
  for +q: B.Number64
  {last_before(n, C.one64(q), C.decrease64(q)) == N.last(1n+n, q) : Bool}
def last_before_reconstitute_o_protocol_counted(n, q):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Bool, Bool, r => Bool.not(C.one64(q)) && r,
        last_before(p, C.one64(C.decrease64(q)), C.decrease64(C.decrease64(q))), N.last(1n+p, C.decrease64(q)),
        last_before_reconstitute_o_protocol_counted(p, C.decrease64(q)))

# Snapshot immediately BEFORE emission. Does not assumes emission
# produces DecodedReady or that the suffix is empty. Isolates the final scalar.
type EmissionContent<-bs: List<&2, U32>, -body: B.Number64, -ceiling: B.Number64,
  -name: Bool, -last: Bool, -q: B.Number64, -u: C.Unicode,
  -inverted: String, -stack: C.Stack, -v: D.Value> is Type:
  EmissionContent{before: List<&2, U32>, byte: U32, suffix: List<&2, U32>,
    body_before: B.Number64, ceiling_before: B.Number64, q_before: B.Number64,
    unicode_before: C.Unicode, inverted_before: String, code: U32,
    division: {bs == B.concatenate(before, Con{byte, suffix}) : List<&2, U32>},
    count: {last_before(B.length(before), last, q) == True{} : Bool},
    snapshot: {R.execute(before, R.Frame{body, ceiling, C.Content{name, last, q, u, inverted, stack}}) ==
      R.Frame{body_before, ceiling_before, C.Content{name, True{}, q_before, unicode_before, inverted_before, stack}} : R.Frame},
    scalar: {C.step_utf8(unicode_before, byte) == C.Character{code} : C.Scalar},
    transduction: {U.traverse_text(before, U.Reading{u, inverted}) == U.Reading{unicode_before, inverted_before} : U.TextValue},
    continuation: {R.machine(R.execute(suffix,
      R.Frame{C.decrease64(body_before), C.decrease64(ceiling_before),
        C.emit_text(name, String.reverse(SCon{Chr{code}, inverted_before}), stack)})) == C.DecodedReady{v} : C.Machine}}

# Appends a byte that has not emitted yet, preserving the snapshot and
# continuation obtained by induction on the byte tail.
def precede_emission(+b: U32, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +name: Bool, +q: B.Number64, +u: C.Unicode, +inverted: String, +stack: C.Stack,
  +next: C.Unicode, +text: String, -v: D.Value,
  step: {C.store_scalar(C.step_utf8(u, b), False{}, name, q, inverted, stack) ==
    C.Content{name, C.one64(q), C.decrease64(q), next, text, stack} : C.Machine},
  transition: {U.step_text(U.Reading{u, inverted}, b) == U.Reading{next, text} : U.TextValue},
  emission: EmissionContent<bs, C.decrease64(body), C.decrease64(ceiling), name,
    C.one64(q), C.decrease64(q), next, text, stack, v>) ->
  EmissionContent<Con{b, bs}, body, ceiling, name, False{}, q, u, inverted, stack, v>:
  match emission:
    case EmissionContent{+before, +byte, +suffix, +ca, +ta, +qa, +ua, +ia, +cp,
      division, count, snapshot, scalar, transduction, continuation}:
      EmissionContent{Con{b, before}, byte, suffix, ca, ta, qa, ua, ia, cp,
        Equal.cong(List<&2, U32>, List<&2, U32>, r => Con{b, r}, bs, B.concatenate(before, Con{byte, suffix}), division),
        count,
        (%Equal.sym(C.Machine,
          C.store_scalar(C.step_utf8(u, b), False{}, name, q, inverted, stack),
          C.Content{name, C.one64(q), C.decrease64(q), next, text, stack}, step) :
          {R.execute(before, R.Frame{C.decrease64(body), C.decrease64(ceiling), _}) ==
            R.Frame{ca, ta, C.Content{name, True{}, qa, ua, ia, stack}} : R.Frame}
          snapshot),
        scalar,
        (%Equal.sym(U.TextValue, U.step_text(U.Reading{u, inverted}, b), U.Reading{next, text}, transition) :
          {U.traverse_text(before, _) == U.Reading{ua, ia} : U.TextValue}
          transduction),
        continuation}

def extract_step_content(+e: C.Scalar, last: Bool,
  +b: U32, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +name: Bool, +q: B.Number64, +u: C.Unicode, +inverted: String, +stack: C.Stack, -v: D.Value,
  +scalar: {C.step_utf8(u, b) == e : C.Scalar},
  accepted: {R.machine(R.execute(bs, R.Frame{C.decrease64(body), C.decrease64(ceiling),
    C.store_scalar(e, last, name, q, inverted, stack)})) == C.DecodedReady{v} : C.Machine},
  resume: @next: C.Unicode -> @text: String ->
    {R.machine(R.execute(bs, R.Frame{C.decrease64(body), C.decrease64(ceiling),
      C.Content{name, C.one64(q), C.decrease64(q), next, text, stack}})) == C.DecodedReady{v} : C.Machine} ->
    EmissionContent<bs, C.decrease64(body), C.decrease64(ceiling), name,
      C.one64(q), C.decrease64(q), next, text, stack, v>) ->
  EmissionContent<Con{b, bs}, body, ceiling, name, last, q, u, inverted, stack, v>:
  match e last:
    case C.UTFInvalid{} +last:
      invalid_negative_terminates_ready(EmissionContent<Con{b, bs}, body, ceiling, name, last, q, u, inverted, stack, v>,
        bs, C.decrease64(body), C.decrease64(ceiling), v, accepted)
    case C.Partial{next} True{}:
      invalid_negative_terminates_ready(EmissionContent<Con{b, bs}, body, ceiling, name, True{}, q, u, inverted, stack, v>,
        bs, C.decrease64(body), C.decrease64(ceiling), v, accepted)
    case C.Character{+cp} True{}:
      EmissionContent{[], b, bs, body, ceiling, q, u, inverted, cp, {==}, {==}, {==}, scalar, {==}, accepted}
    case C.Character{+cp} False{}:
      precede_emission(b, bs, body, ceiling, name, q, u, inverted, stack, C.Start{}, SCon{Chr{cp}, inverted}, v,
        Equal.cong(C.Scalar, C.Machine, x => C.store_scalar(x, False{}, name, q, inverted, stack),
          C.step_utf8(u, b), C.Character{cp}, scalar),
        Equal.cong(C.Scalar, U.TextValue, x => U.join(x, inverted), C.step_utf8(u, b), C.Character{cp}, scalar),
        resume(C.Start{}, SCon{Chr{cp}, inverted}, accepted))
    case C.Partial{+next} False{}:
      precede_emission(b, bs, body, ceiling, name, q, u, inverted, stack, next, inverted, v,
        Equal.cong(C.Scalar, C.Machine, x => C.store_scalar(x, False{}, name, q, inverted, stack),
          C.step_utf8(u, b), C.Partial{next}, scalar),
        Equal.cong(C.Scalar, U.TextValue, x => U.join(x, inverted), C.step_utf8(u, b), C.Partial{next}, scalar),
        resume(next, inverted, accepted))

law execution_content_accepts_isolates_to_emission:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +name: Bool
  for +last: Bool
  for +q: B.Number64
  for +u: C.Unicode
  for +inverted: String
  for +stack: C.Stack
  for -v: D.Value
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.Content{name, last, q, u, inverted, stack}})) == C.DecodedReady{v} : C.Machine}
  EmissionContent<bs, body, ceiling, name, last, q, u, inverted, stack, v>
def execution_content_accepts_isolates_to_emission(bs, body, ceiling, name, last, q, u, inverted, stack, v, accepted):
  match bs:
    case Nil{}:
      L.ex_false(EmissionContent<Nil{}, body, ceiling, name, last, q, u, inverted, stack, v>,
        F.false_negative_true(Equal.cong(C.Machine, Bool, m => ready(m),
          C.Content{name, last, q, u, inverted, stack}, C.DecodedReady{v}, accepted)))
    case Con{+b, +tail}:
      extract_step_content(C.step_utf8(u, b), last, b, tail, body, ceiling, name, q, u, inverted, stack, v, {==}, accepted,
        next => text => accepts_tail => execution_content_accepts_isolates_to_emission(tail,
          C.decrease64(body), C.decrease64(ceiling), name, C.one64(q), C.decrease64(q), next, text, stack, v, accepts_tail))

law length_until_o_byte_final:
  for +before: List<&2, U32>
  for +byte: U32
  {B.length(B.concatenate(before, [byte])) == 1n+B.length(before) : Nat}
def length_until_o_byte_final(before, byte):
  match before:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(Nat, Nat, n => 1n+n, B.length(B.concatenate(t, [byte])), 1n+B.length(t),
        length_until_o_byte_final(t, byte))

law divide_before_and_later_of_byte_final:
  for before: List<&2, U32>
  for +byte: U32
  for +suffix: List<&2, U32>
  {B.concatenate(before, Con{byte, suffix}) == B.concatenate(B.concatenate(before, [byte]), suffix) : List<&2, U32>}
def divide_before_and_later_of_byte_final(before, byte, suffix):
  match before:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, bs => Con{h, bs},
        B.concatenate(t, Con{byte, suffix}), B.concatenate(B.concatenate(t, [byte]), suffix),
        divide_before_and_later_of_byte_final(t, byte, suffix))

def prefix_until_o_byte_final_has_bytes(before: List<&2, U32>, byte: U32) -> G.NotEmpty(B.concatenate(before, [byte])):
  match before:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      Unit{}

law transduction_textual_of_concatenation:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: U.TextValue
  {U.traverse_text(B.concatenate(xs, ys), t) == U.traverse_text(ys, U.traverse_text(xs, t)) : U.TextValue}
def transduction_textual_of_concatenation(xs, ys, t):
  match xs:
    case Nil{}:
      {==}
    case Con{b, tail}:
      transduction_textual_of_concatenation(tail, ys, U.step_text(t, b))

def protocol_content(n: Nat, last: Bool, q: B.Number64) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      last_before(p, last, q)

law protocol_content_normalized_reconstitutes_last:
  for n: Nat
  for +q: B.Number64
  {protocol_content(n, C.one64(q), C.decrease64(q)) == N.last(n, q) : Bool}
def protocol_content_normalized_reconstitutes_last(n, q):
  match n:
    case 0n:
      {==}
    case 1n+p:
      last_before_reconstitute_o_protocol_counted(p, q)

law protocol_content_accepted_reconstructs_count_original:
  for +content: List<&2, U32>
  for +q: B.Number64
  for checked: {protocol_content(B.length(content), C.one64(q), C.decrease64(q)) == True{} : Bool}
  {B.nat64(B.length(content)) == Some{q} : Maybe<&2, B.Number64>}
def protocol_content_accepted_reconstructs_count_original(content, q, checked):
  N.last_accepted_reconstruct_to_count_original(B.length(content), q,
    Equal.trans(Bool, N.last(B.length(content), q),
      protocol_content(B.length(content), C.one64(q), C.decrease64(q)), True{},
      Equal.sym(Bool, protocol_content(B.length(content), C.one64(q), C.decrease64(q)),
        N.last(B.length(content), q), protocol_content_normalized_reconstitutes_last(B.length(content), q)), checked))

# Form usable by soundness: content bytes, reencoded text,
# frame after emit_text and suffix execution are joint witnesses.
# last/q remain arbitrary; the protocol is a CONCLUSION of acceptance.
type PrefixTextAccepted<-bs: List<&2, U32>, -body: B.Number64, -ceiling: B.Number64,
  -name: Bool, -last: Bool, -q: B.Number64, -stack: C.Stack, -v: D.Value> is Type:
  PrefixTextAccepted{content: List<&2, U32>, suffix: List<&2, U32>, text: String,
    body_emission: B.Number64, ceiling_emission: B.Number64,
    division: {bs == B.concatenate(content, suffix) : List<&2, U32>},
    positive: G.NotEmpty(content),
    bytes: {B.utf8(text) == content : List<&2, U32>},
    transduction: {U.finalize_text(U.traverse_text(content, U.Reading{C.Start{}, ""})) == Some{text} : Maybe<&2, String>},
    protocol: {protocol_content(B.length(content), last, q) == True{} : Bool},
    emission: {R.execute(content, R.Frame{body, ceiling, C.Content{name, last, q, C.Start{}, "", stack}}) ==
      R.Frame{body_emission, ceiling_emission, C.emit_text(name, text, stack)} : R.Frame},
    continuation: {R.machine(R.execute(suffix,
      R.Frame{body_emission, ceiling_emission, C.emit_text(name, text, stack)})) == C.DecodedReady{v} : C.Machine}}

def transduction_until_emission(+before: List<&2, U32>, +byte: U32,
  +u: C.Unicode, +inverted: String, +cp: U32,
  transduction: {U.traverse_text(before, U.Reading{C.Start{}, ""}) == U.Reading{u, inverted} : U.TextValue},
  scalar: {C.step_utf8(u, byte) == C.Character{cp} : C.Scalar}) ->
  {U.finalize_text(U.traverse_text(B.concatenate(before, [byte]), U.Reading{C.Start{}, ""})) ==
    Some{String.reverse(SCon{Chr{cp}, inverted})} : Maybe<&2, String>}:
  %Equal.sym(U.TextValue, U.traverse_text(B.concatenate(before, [byte]), U.Reading{C.Start{}, ""}),
    U.traverse_text([byte], U.traverse_text(before, U.Reading{C.Start{}, ""})),
    transduction_textual_of_concatenation(before, [byte], U.Reading{C.Start{}, ""})) :
    {U.finalize_text(_) == Some{String.reverse(SCon{Chr{cp}, inverted})} : Maybe<&2, String>}
  %Equal.sym(U.TextValue, U.traverse_text(before, U.Reading{C.Start{}, ""}), U.Reading{u, inverted}, transduction) :
    {U.finalize_text(U.traverse_text([byte], _)) == Some{String.reverse(SCon{Chr{cp}, inverted})} : Maybe<&2, String>}
  Equal.cong(C.Scalar, Maybe<&2, String>, e => U.finalize_text(U.join(e, inverted)),
    C.step_utf8(u, byte), C.Character{cp}, scalar)

def execute_until_emission(+before: List<&2, U32>, +byte: U32,
  +body: B.Number64, +ceiling: B.Number64, +name: Bool, +last: Bool, +q: B.Number64, +stack: C.Stack,
  +ca: B.Number64, +ta: B.Number64, +qa: B.Number64, +ua: C.Unicode, +ia: String, +cp: U32,
  snapshot: {R.execute(before, R.Frame{body, ceiling, C.Content{name, last, q, C.Start{}, "", stack}}) ==
    R.Frame{ca, ta, C.Content{name, True{}, qa, ua, ia, stack}} : R.Frame},
  scalar: {C.step_utf8(ua, byte) == C.Character{cp} : C.Scalar}) ->
  {R.execute(B.concatenate(before, [byte]), R.Frame{body, ceiling, C.Content{name, last, q, C.Start{}, "", stack}}) ==
    R.Frame{C.decrease64(ca), C.decrease64(ta), C.emit_text(name, String.reverse(SCon{Chr{cp}, ia}), stack)} : R.Frame}:
  %Equal.sym(R.Frame,
    R.execute(B.concatenate(before, [byte]), R.Frame{body, ceiling, C.Content{name, last, q, C.Start{}, "", stack}}),
    R.execute([byte], R.execute(before, R.Frame{body, ceiling, C.Content{name, last, q, C.Start{}, "", stack}})),
    R.execution_of_concatenation(before, [byte], R.Frame{body, ceiling, C.Content{name, last, q, C.Start{}, "", stack}})) :
    {_ == R.Frame{C.decrease64(ca), C.decrease64(ta), C.emit_text(name, String.reverse(SCon{Chr{cp}, ia}), stack)} : R.Frame}
  %Equal.sym(R.Frame,
    R.execute(before, R.Frame{body, ceiling, C.Content{name, last, q, C.Start{}, "", stack}}),
    R.Frame{ca, ta, C.Content{name, True{}, qa, ua, ia, stack}}, snapshot) :
    {R.execute([byte], _) == R.Frame{C.decrease64(ca), C.decrease64(ta), C.emit_text(name, String.reverse(SCon{Chr{cp}, ia}), stack)} : R.Frame}
  Equal.cong(C.Scalar, R.Frame,
    e => R.Frame{C.decrease64(ca), C.decrease64(ta), C.store_scalar(e, True{}, name, qa, ia, stack)},
    C.step_utf8(ua, byte), C.Character{cp}, scalar)

def reencode_emission(+bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +name: Bool, +last: Bool, +q: B.Number64, +stack: C.Stack, -v: D.Value,
  event: EmissionContent<bs, body, ceiling, name, last, q, C.Start{}, "", stack, v>) ->
  PrefixTextAccepted<bs, body, ceiling, name, last, q, stack, v>:
  match event:
    case EmissionContent{+before, +byte, +suffix, +ca, +ta, +qa, +ua, +ia, +cp,
      division, count, snapshot, +scalar, transduction, continuation}:
      +content = B.concatenate(before, [byte])
      +text = String.reverse(SCon{Chr{cp}, ia})
      +transduced = transduction_until_emission(before, byte, ua, ia, cp, transduction, scalar)
      PrefixTextAccepted{content, suffix, text, C.decrease64(ca), C.decrease64(ta),
        Equal.trans(List<&2, U32>, bs, B.concatenate(before, Con{byte, suffix}), B.concatenate(content, suffix),
          division, divide_before_and_later_of_byte_final(before, byte, suffix)),
        prefix_until_o_byte_final_has_bytes(before, byte),
        I.utf8_input_accepts_reencodes_exactly(content, text, transduced), transduced,
        (%Equal.sym(Nat, B.length(content), 1n+B.length(before), length_until_o_byte_final(before, byte)) :
          {protocol_content(_, last, q) == True{} : Bool}
          count),
        execute_until_emission(before, byte, body, ceiling, name, last, q, stack, ca, ta, qa, ua, ia, cp, snapshot, scalar),
        continuation}

law content_accepted_extracts_prefix_textual:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +name: Bool
  for +last: Bool
  for +q: B.Number64
  for +stack: C.Stack
  for -v: D.Value
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.Content{name, last, q, C.Start{}, "", stack}})) == C.DecodedReady{v} : C.Machine}
  PrefixTextAccepted<bs, body, ceiling, name, last, q, stack, v>
def content_accepted_extracts_prefix_textual(bs, body, ceiling, name, last, q, stack, v, accepted):
  reencode_emission(bs, body, ceiling, name, last, q, stack, v,
    execution_content_accepts_isolates_to_emission(bs, body, ceiling, name, last, q, C.Start{}, "", stack, v, accepted))

# q is the ORIGINAL header count, not an assumed measure.
# The reconstructed protocol above proves that nat64 of the content is Some q.
type ContentCountedAccepted<-bs: List<&2, U32>, -body: B.Number64, -ceiling: B.Number64,
  -name: Bool, -q: B.Number64, -stack: C.Stack, -v: D.Value> is Type:
  ContentCountedAccepted{content: List<&2, U32>, suffix: List<&2, U32>, text: String,
    body_emission: B.Number64, ceiling_emission: B.Number64,
    division: {bs == B.concatenate(content, suffix) : List<&2, U32>},
    positive: G.NotEmpty(content),
    bytes: {B.utf8(text) == content : List<&2, U32>},
    measure: {B.nat64(B.length(content)) == Some{q} : Maybe<&2, B.Number64>},
    transduction: {U.finalize_text(U.traverse_text(content, U.Reading{C.Start{}, ""})) == Some{text} : Maybe<&2, String>},
    emission: {R.execute(content, R.Frame{body, ceiling,
      C.Content{name, C.one64(q), C.decrease64(q), C.Start{}, "", stack}}) ==
      R.Frame{body_emission, ceiling_emission, C.emit_text(name, text, stack)} : R.Frame},
    continuation: {R.machine(R.execute(suffix,
      R.Frame{body_emission, ceiling_emission, C.emit_text(name, text, stack)})) == C.DecodedReady{v} : C.Machine}}

def measure_prefix_extracted(-bs: List<&2, U32>, -body: B.Number64, -ceiling: B.Number64,
  -name: Bool, +q: B.Number64, -stack: C.Stack, -v: D.Value,
  extracted: PrefixTextAccepted<bs, body, ceiling, name, C.one64(q), C.decrease64(q), stack, v>) ->
  ContentCountedAccepted<bs, body, ceiling, name, q, stack, v>:
  match extracted:
    case PrefixTextAccepted{+content, suffix, text, ca, ta, division, positive, bytes, transduction, protocol, emission, continuation}:
      ContentCountedAccepted{content, suffix, text, ca, ta, division, positive, bytes,
        protocol_content_accepted_reconstructs_count_original(content, q, protocol), transduction, emission, continuation}

law content_counted_accepted_reconstructs_prefix_text_and_count:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +name: Bool
  for +q: B.Number64
  for +stack: C.Stack
  for -v: D.Value
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling,
    C.Content{name, C.one64(q), C.decrease64(q), C.Start{}, "", stack}})) == C.DecodedReady{v} : C.Machine}
  ContentCountedAccepted<bs, body, ceiling, name, q, stack, v>
def content_counted_accepted_reconstructs_prefix_text_and_count(bs, body, ceiling, name, q, stack, v, accepted):
  measure_prefix_extracted(bs, body, ceiling, name, q, stack, v,
    content_accepted_extracts_prefix_textual(bs, body, ceiling, name, C.one64(q), C.decrease64(q), stack, v, accepted))
