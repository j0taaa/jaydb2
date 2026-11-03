# BE64 word extraction from actual execution, for every purpose
# and stack. Byte validity follows from decode prechecks;
# R.execute alone does not check U32 <= 255.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecWordsBE64.bend as H
import ./CodecWordsInverse.bend as I

def start(f: C.Purpose, stack: C.Stack, body: B.Number64, ceiling: B.Number64) -> R.Frame:
  R.Frame{body, ceiling, C.WordInput{f, 7n, 0, 0, stack}}

def after_word(f: C.Purpose, high: U32, low: U32, stack: C.Stack,
  +body: B.Number64, +ceiling: B.Number64) -> R.Frame:
  R.Frame{H.decrease(8n, body), H.decrease(8n, ceiling),
    C.conclude_word(f, high, low, stack, H.decrease(8n, body), H.decrease(8n, ceiling))}

# The missing counter stores bytes AFTER the next: missing=0
# still requires one byte. This shape follows from execution, not a premise
# of the public extraction theorem.
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

law word_ready_requires_prefix_complete:
  for n: Nat
  for +bs: List<&2, U32>
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for ready: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.WordInput{f, n, high, low, stack}})) == C.DecodedReady{v} : C.Machine}
  WordSufficient(n, bs)
def word_ready_requires_prefix_complete(n, bs, f, high, low, stack, body, ceiling, v, ready):
  match n bs:
    case 0n Nil{}:
      R.input_negative_decoded(v,
        Equal.cong(C.Machine, C.Outcome, m => C.finalize(m),
          C.WordInput{f, 0n, high, low, stack}, C.DecodedReady{v}, ready))
    case 0n Con{b, t}:
      Unit{}
    case 1n+p Nil{}:
      R.input_negative_decoded(v,
        Equal.cong(C.Machine, C.Outcome, m => C.finalize(m),
          C.WordInput{f, 1n+p, high, low, stack}, C.DecodedReady{v}, ready))
    case 1n+p Con{+b, +t}:
      word_ready_requires_prefix_complete(p, t, f,
        (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32),
        stack, C.decrease64(body), C.decrease64(ceiling), v, ready)

# Separates validity of the ORIGINAL prefix and suffix; no reencoding
# or canonicity assumption participates in this stage.
def join_validity_of_octets(-b: U32, -t: List<&2, U32>, -ys: List<&2, U32>,
  vb: {U32.is_le(b, 255) == True{} : Bool},
  pair: L.E<{B.octets_all_valid(t) == True{} : Bool}, {B.octets_all_valid(ys) == True{} : Bool}>) ->
  L.E<{B.octets_all_valid(Con{b, t}) == True{} : Bool}, {B.octets_all_valid(ys) == True{} : Bool}>:
  match pair:
    case L.Both{vt, vy}:
      L.Both{F.and_boolean_intro(U32.is_le(b, 255), B.octets_all_valid(t), vb, vt), vy}

law separate_octets_all_valid:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +all_valid: {B.octets_all_valid(B.concatenate(xs, ys)) == True{} : Bool}
  L.E<{B.octets_all_valid(xs) == True{} : Bool}, {B.octets_all_valid(ys) == True{} : Bool}>
def separate_octets_all_valid(xs, ys, all_valid):
  match xs:
    case Nil{}:
      L.Both{{==}, all_valid}
    case Con{+b, +t}:
      join_validity_of_octets(b, t, ys,
        F.and_boolean_left(U32.is_le(b, 255), B.octets_all_valid(B.concatenate(t, ys)), all_valid),
        separate_octets_all_valid(t, ys,
          F.and_boolean_right(U32.is_le(b, 255), B.octets_all_valid(B.concatenate(t, ys)), all_valid)))

# a..h are the eight U32 values of the received list. high/low are computed by
# accumulate, and be64 later proves that it reencodes these same
# bytes. execution preserves the ENTIRE final frame, including counters.
type WordExtracted<-bs: List<&2, U32>, -f: C.Purpose, -stack: C.Stack,
  -body: B.Number64, -ceiling: B.Number64, -v: D.Value> is Type:
  Extracted{a: U32, b: U32, c: U32, d: U32, e: U32, f0: U32, g: U32, h: U32,
    suffix: List<&2, U32>, high: U32, low: U32,
    factoring: {bs == B.concatenate([a, b, c, d, e, f0, g, h], suffix) : List<&2, U32>},
    octets: {B.octets_all_valid([a, b, c, d, e, f0, g, h]) == True{} : Bool},
    rest_valid: {B.octets_all_valid(suffix) == True{} : Bool},
    number: {I.accumulate([a, b, c, d, e, f0, g, h], B.Number64{0, 0}) == B.Number64{high, low} : B.Number64},
    be64: {B.be64(high, low) == [a, b, c, d, e, f0, g, h] : List<&2, U32>},
    factoring_be64: {bs == B.concatenate(B.be64(high, low), suffix) : List<&2, U32>},
    frame: {R.execute([a, b, c, d, e, f0, g, h], start(f, stack, body, ceiling)) == after_word(f, high, low, stack, body, ceiling) : R.Frame},
    execution: {R.execute(suffix, after_word(f, high, low, stack, body, ceiling)) == R.execute(bs, start(f, stack, body, ceiling)) : R.Frame},
    ready: {R.machine(R.execute(suffix, after_word(f, high, low, stack, body, ceiling))) == C.DecodedReady{v} : C.Machine}}

def extract_eight_octets(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f0: U32, +g: U32, +h: U32, +suffix: List<&2, U32>,
  +f: C.Purpose, +stack: C.Stack, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  ready: {R.machine(R.execute(B.concatenate([a, b, c, d, e, f0, g, h], suffix), start(f, stack, body, ceiling))) == C.DecodedReady{v} : C.Machine},
  pair: L.E<{B.octets_all_valid([a, b, c, d, e, f0, g, h]) == True{} : Bool},
    {B.octets_all_valid(suffix) == True{} : Bool}>) ->
  WordExtracted<B.concatenate([a, b, c, d, e, f0, g, h], suffix), f, stack, body, ceiling, v>:
  match pair:
    case L.Both{+octets, rest_valid}:
      +frame = I.eight_octets_all_valid_conclude_word(f, a, b, c, d, e, f0, g, h, stack, body, ceiling, octets)
      +execution = Equal.sym(R.Frame,
        R.execute(B.concatenate([a, b, c, d, e, f0, g, h], suffix), start(f, stack, body, ceiling)),
        R.execute(suffix, after_word(f, I.assemble(a, b, c, d), I.assemble(e, f0, g, h), stack, body, ceiling)),
        Equal.trans(R.Frame,
          R.execute(B.concatenate([a, b, c, d, e, f0, g, h], suffix), start(f, stack, body, ceiling)),
          R.execute(suffix, R.execute([a, b, c, d, e, f0, g, h], start(f, stack, body, ceiling))),
          R.execute(suffix, after_word(f, I.assemble(a, b, c, d), I.assemble(e, f0, g, h), stack, body, ceiling)),
          R.execution_of_concatenation([a, b, c, d, e, f0, g, h], suffix, start(f, stack, body, ceiling)),
          Equal.cong(R.Frame, R.Frame, q => R.execute(suffix, q),
            R.execute([a, b, c, d, e, f0, g, h], start(f, stack, body, ceiling)),
            after_word(f, I.assemble(a, b, c, d), I.assemble(e, f0, g, h), stack, body, ceiling), frame)))
      +be64 = I.be64_reencodes_eight_octets_all_valid(a, b, c, d, e, f0, g, h, octets)
      Extracted{a, b, c, d, e, f0, g, h, suffix, I.assemble(a, b, c, d), I.assemble(e, f0, g, h),
        {==}, octets, rest_valid,
        I.accumulate_eight_octets_all_valid(a, b, c, d, e, f0, g, h, octets), be64,
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => B.concatenate(xs, suffix),
          [a, b, c, d, e, f0, g, h], B.be64(I.assemble(a, b, c, d), I.assemble(e, f0, g, h)),
          Equal.sym(List<&2, U32>, B.be64(I.assemble(a, b, c, d), I.assemble(e, f0, g, h)), [a, b, c, d, e, f0, g, h], be64)),
        frame, execution,
        Equal.trans(C.Machine,
          R.machine(R.execute(suffix, after_word(f, I.assemble(a, b, c, d), I.assemble(e, f0, g, h), stack, body, ceiling))),
          R.machine(R.execute(B.concatenate([a, b, c, d, e, f0, g, h], suffix), start(f, stack, body, ceiling))), C.DecodedReady{v},
          Equal.cong(R.Frame, C.Machine, q => R.machine(q),
            R.execute(suffix, after_word(f, I.assemble(a, b, c, d), I.assemble(e, f0, g, h), stack, body, ceiling)),
            R.execute(B.concatenate([a, b, c, d, e, f0, g, h], suffix), start(f, stack, body, ceiling)), execution), ready)}

def extract_word_combined_format(+bs: List<&2, U32>, +f: C.Purpose, +stack: C.Stack,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  all_valid: {B.octets_all_valid(bs) == True{} : Bool},
  ready: {R.machine(R.execute(bs, start(f, stack, body, ceiling))) == C.DecodedReady{v} : C.Machine},
  format: WordSufficient(7n, bs)) -> WordExtracted<bs, f, stack, body, ceiling, v>:
  match bs:
    case Nil{}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{a, Nil{}}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{a, Con{b, Nil{}}}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{a, Con{b, Con{c, Nil{}}}}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f0, Nil{}}}}}}}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f0, Con{g, Nil{}}}}}}}}:
      L.ex_false(WordExtracted<bs, f, stack, body, ceiling, v>, format)
    case Con{+a, Con{+b, Con{+c, Con{+d, Con{+e, Con{+f0, Con{+g, Con{+h, +suffix}}}}}}}}:
      extract_eight_octets(a, b, c, d, e, f0, g, h, suffix, f, stack, body, ceiling, v, ready,
        separate_octets_all_valid([a, b, c, d, e, f0, g, h], suffix, all_valid))

# Premises: valid bytes and ACTUALLY reaching DecodedReady. No shape of bs,
# BE64 number, body/ceiling sufficiency or canonicity is assumed.
law word_accepts_extracts_be64_and_execution_remaining:
  for +bs: List<&2, U32>
  for +f: C.Purpose
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for +ready: {R.machine(R.execute(bs, start(f, stack, body, ceiling))) == C.DecodedReady{v} : C.Machine}
  WordExtracted<bs, f, stack, body, ceiling, v>
def word_accepts_extracts_be64_and_execution_remaining(bs, f, stack, body, ceiling, v, all_valid, ready):
  extract_word_combined_format(bs, f, stack, body, ceiling, v, all_valid, ready,
    word_ready_requires_prefix_complete(7n, bs, f, 0, 0, stack, body, ceiling, v, ready))
