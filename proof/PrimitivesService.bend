# Primitive core calls, without publication or conclusion tags.
import Base
import ./ProtocolService.bend as Q
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../src/Codec.bend as C
import ../src/State.bend as E
import ./CodecRefusals.bend as R
import ./CodecSums64.bend as W
import ./Foundations.bend as F

# Fields are recorded by the actual parser step.
type Primitive is Data:
  Prefix{count: Nat, original: Primitive}
  Encode{value: D.Value}
  Decode{bytes: List<&2, U32>, ceiling: B.Number64}
  Store{schema: D.Schema, state: D.State}
  Read{before: Nat, capacity: Nat, received: Nat, declared: Nat}

# Variable-field opening uses the actual function's check.
def check(f: C.Purpose, high: U32, low: U32,
  stack: C.Stack, body: B.Number64, ceiling: B.Number64) -> C.Check:
  C.check(C.sum_optional(C.minimum_field(f, B.Number64{high, low}),
    C.minimum_stack(stack)), body, ceiling)

def construct(c: C.Check, +pos: Nat, +n: Nat) -> List<&2, Q.Frame>:
  match c:
    case C.Fits{}: [Q.Checked{pos, n}, Q.Constructed{pos, n}]
    case _: Nil{}

# Store denotes serialization/copy of the published snapshot or already-valid
# success proposal. It does not denote private-state stores in the
# machine: those follow Core/Operated and official compiler faithfulness.
# Abstraction is the actual State.decode function, not state repeated by definition.
def store_abstraction(q: Maybe<&2, D.State>, s: D.State, bs: List<&2, U32>) -> List<&2, Q.Frame>:
  match q:
    case None{}: Nil{}
    case Some{a}: [Q.Stored{s, bs, a}]

def store_bytes(q: Maybe<&2, List<&2, U32>>, e: D.Schema, +s: D.State) -> List<&2, Q.Frame>:
  match q:
    case None{}: Nil{}
    case Some{bs}: store_abstraction(E.decode(D.state_value(s), e), s, bs)

def count(high: U32, low: U32) -> Nat:
  Word.to_nat(64n, W.bits(B.Number64{high, low}))

def open_name_valid(f: C.Purpose, +high: U32, +low: U32) -> Bool:
  match f:
    case C.Integer{}: False{}
    case C.NameText{}:
      Bool.not(C.zero64(B.Number64{high, low})) && C.less_equal64(B.Number64{high, low}, B.Number64{0, 64})
    case _: True{}

def open_field(c: C.Check, ready: Bool, +pos: Nat, +n: Nat) -> List<&2, Q.Frame>:
  match c ready:
    case C.Fits{} True{}: construct(C.Fits{}, pos, n)
    case C.Fits{} False{}: [Q.Checked{pos, n}]
    case _ _: Nil{}

def frame_field(+pos: Nat, +f: C.Purpose, +high: U32, +low: U32, stack: C.Stack,
  body: B.Number64, ceiling: B.Number64) -> List<&2, Q.Frame>:
  open_field(check(f, high, low, stack, body, ceiling), open_name_valid(f, high, low),
    pos, count(high, low))

# This is the actual Codec step; it only records its field openings.
def frame_tag(tag: Nat, pos: Nat) -> List<&2, Q.Frame>:
  match tag:
    case 0n: construct(C.Fits{}, pos, 1n)
    case 1n: construct(C.Fits{}, pos, 1n)
    case 2n: construct(C.Fits{}, pos, 1n)
    case 3n+k: Nil{}

def frame_word(+f: C.Purpose, +high: U32, +low: U32, stack: C.Stack,
  body: B.Number64, ceiling: B.Number64, pos: Nat) -> List<&2, Q.Frame>:
  match f:
    case C.Integer{}: construct(C.Fits{}, pos, 8n)
    case C.TextValue{}: frame_field(pos, C.TextValue{}, high, low, stack, body, ceiling)
    case C.NameText{}: frame_field(pos, C.NameText{}, high, low, stack, body, ceiling)
    case C.CountsList{}: frame_field(pos, C.CountsList{}, high, low, stack, body, ceiling)
    case C.CountsRecord{}: frame_field(pos, C.CountsRecord{}, high, low, stack, body, ceiling)

def frame_step(m: C.Machine, +b: U32, body: B.Number64, ceiling: B.Number64, pos: Nat) -> List<&2, Q.Frame>:
  match m:
    case C.Tag{stack}: frame_tag(U32.to_nat(b), pos)
    case C.WordInput{f, 0n, high, +low, stack}:
      frame_word(f, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), stack, body, ceiling, pos)
    case C.TagName{stack}: Nil{}
    case C.WordInput{f, 1n+n, high, low, stack}: Nil{}
    case C.Content{name, last, q, u, text, stack}: Nil{}
    case C.DecodedReady{v}: Nil{}
    case C.Invalid{}: Nil{}
    case C.Above{}: Nil{}

def frames_codec(bs: List<&2, U32>, +m: C.Machine, +body: B.Number64, +ceiling: B.Number64, +pos: Nat) -> List<&2, Q.Frame>:
  match bs:
    case Nil{}: Nil{}
    case Con{+b, t}: Q.concatenate(frame_step(m, b, C.decrease64(body), C.decrease64(ceiling), pos), frames_codec(t, C.step(m, b, C.decrease64(body), C.decrease64(ceiling)), C.decrease64(body), C.decrease64(ceiling), Succ{pos}))

def decoding_admitted(ok: Bool, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64) -> List<&2, Q.Frame>:
  match ok:
    case False{}: Nil{}
    case True{}: Q.concatenate(frames_codec(bs, C.Tag{C.Root{}}, body, ceiling, 0n),
      [Q.Decoded{bs, R.optional(C.decode(bs, ceiling))}])

def decoding_measure(q: Maybe<&2, B.Number64>, +bs: List<&2, U32>, +ceiling: B.Number64) -> List<&2, Q.Frame>:
  match q:
    case None{}: Nil{}
    case Some{+body}: decoding_admitted(C.less_equal64(body, ceiling) && B.octets_all_valid(bs), bs, body, ceiling)

def expand(q: Primitive) -> List<&2, Q.Frame>:
  match q:
    case Prefix{n, p}: Q.first(n, expand(p))
    case Encode{+v}: [Q.Encoded{v, P.encode(v)}]
    case Decode{+bs, ceiling}: decoding_measure(B.nat64(B.length(bs)), bs, ceiling)
    case Store{e, +s}: store_bytes(P.encode(D.state_value(s)), e, s)
    case Read{before, cap, received, declared}: [Q.Read{before, received, declared}]

def expand_primitives(xs: List<&2, Primitive>) -> List<&2, Q.Frame>:
  match xs:
    case Nil{}: Nil{}
    case Con{h, t}: Q.concatenate(expand(h), expand_primitives(t))

# Prevents the subtrace from storing or concluding the call.
def internal(q: Q.Frame) -> Bool:
  match q:
    case Q.Encoded{v, bs}: True{}
    case Q.Decoded{bs, v}: True{}
    case Q.Stored{s, bs, abstr}: True{}
    case Q.Checked{p, n}: True{}
    case Q.Constructed{p, n}: True{}
    case Q.Read{before, n, declared}: True{}
    case _: False{}

def Internal(qs: List<&2, Q.Frame>) -> Type:
  match qs:
    case Nil{}: Unit
    case Con{h, t}: L.E<{internal(h) == True{} : Bool}, Internal(t)>

law concatenate_internal:
  for xs: List<&2, Q.Frame>
  for -ys: List<&2, Q.Frame>
  for a: Internal(xs)
  for b: Internal(ys)
  Internal(Q.concatenate(xs, ys))
def concatenate_internal(xs, ys, a, b):
  match xs a:
    case Nil{} _: b
    case Con{h, t} L.Both{head, tail}:
      L.Both{head, concatenate_internal(t, ys, tail, b)}

law construct_internal:
  for c: C.Check
  for -pos: Nat
  for -n: Nat
  Internal(construct(c, pos, n))
def construct_internal(c, pos, n):
  match c:
    case C.Fits{}: L.Both{{==}, L.Both{{==}, Unit{}}}
    case C.Short{}: Unit{}
    case C.Large{}: Unit{}

def store_abstraction_internal(q: Maybe<&2, D.State>, -s: D.State, -bs: List<&2, U32>) ->
  Internal(store_abstraction(q, s, bs)):
  match q:
    case None{}: Unit{}
    case Some{a}: L.Both{{==}, Unit{}}

def store_bytes_internal(q: Maybe<&2, List<&2, U32>>, +e: D.Schema, +s: D.State) ->
  Internal(store_bytes(q, e, s)):
  match q:
    case None{}: Unit{}
    case Some{bs}: store_abstraction_internal(E.decode(D.state_value(s), e), s, bs)

def open_field_internal(c: C.Check, ready: Bool, -pos: Nat, -n: Nat) ->
  Internal(open_field(c, ready, pos, n)):
  match c ready:
    case C.Fits{} True{}: construct_internal(C.Fits{}, pos, n)
    case C.Fits{} False{}: L.Both{{==}, Unit{}}
    case C.Short{} _: Unit{}
    case C.Large{} _: Unit{}

def frame_field_internal(+pos: Nat, +f: C.Purpose, +high: U32, +low: U32,
  +stack: C.Stack, +body: B.Number64, +ceiling: B.Number64) ->
  Internal(frame_field(pos, f, high, low, stack, body, ceiling)):
  open_field_internal(check(f, high, low, stack, body, ceiling),
    open_name_valid(f, high, low), pos, count(high, low))

def frame_tag_internal(tag: Nat, -pos: Nat) -> Internal(frame_tag(tag, pos)):
  match tag:
    case 0n: construct_internal(C.Fits{}, pos, 1n)
    case 1n: construct_internal(C.Fits{}, pos, 1n)
    case 2n: construct_internal(C.Fits{}, pos, 1n)
    case 3n+k: Unit{}

def frame_word_internal(f: C.Purpose, +high: U32, +low: U32, +stack: C.Stack,
  +body: B.Number64, +ceiling: B.Number64, +pos: Nat) ->
  Internal(frame_word(f, high, low, stack, body, ceiling, pos)):
  match f:
    case C.Integer{}: construct_internal(C.Fits{}, pos, 8n)
    case C.TextValue{}: frame_field_internal(pos, C.TextValue{}, high, low, stack, body, ceiling)
    case C.NameText{}: frame_field_internal(pos, C.NameText{}, high, low, stack, body, ceiling)
    case C.CountsList{}: frame_field_internal(pos, C.CountsList{}, high, low, stack, body, ceiling)
    case C.CountsRecord{}: frame_field_internal(pos, C.CountsRecord{}, high, low, stack, body, ceiling)

def frame_step_internal(m: C.Machine, +b: U32, +body: B.Number64, +ceiling: B.Number64, +pos: Nat) ->
  Internal(frame_step(m, b, body, ceiling, pos)):
  match m:
    case C.Tag{stack}: frame_tag_internal(U32.to_nat(b), pos)
    case C.WordInput{f, 0n, high, +low, stack}:
      frame_word_internal(f, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), stack, body, ceiling, pos)
    case C.TagName{stack}: Unit{}
    case C.WordInput{f, 1n+n, high, low, stack}: Unit{}
    case C.Content{name, last, q, u, text, stack}: Unit{}
    case C.DecodedReady{v}: Unit{}
    case C.Invalid{}: Unit{}
    case C.Above{}: Unit{}

def frames_codec_internal(bs: List<&2, U32>, +m: C.Machine, +body: B.Number64,
  +ceiling: B.Number64, +pos: Nat) -> Internal(frames_codec(bs, m, body, ceiling, pos)):
  match bs:
    case Nil{}: Unit{}
    case Con{+b, +t}:
      concatenate_internal(frame_step(m, b, C.decrease64(body), C.decrease64(ceiling), pos),
        frames_codec(t, C.step(m, b, C.decrease64(body), C.decrease64(ceiling)), C.decrease64(body), C.decrease64(ceiling), Succ{pos}),
        frame_step_internal(m, b, C.decrease64(body), C.decrease64(ceiling), pos),
        frames_codec_internal(t, C.step(m, b, C.decrease64(body), C.decrease64(ceiling)), C.decrease64(body), C.decrease64(ceiling), Succ{pos}))

def decoding_admitted_internal(ok: Bool, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64) ->
  Internal(decoding_admitted(ok, bs, body, ceiling)):
  match ok:
    case False{}: Unit{}
    case True{}: concatenate_internal(frames_codec(bs, C.Tag{C.Root{}}, body, ceiling, 0n),
      [Q.Decoded{bs, R.optional(C.decode(bs, ceiling))}],
      frames_codec_internal(bs, C.Tag{C.Root{}}, body, ceiling, 0n), L.Both{{==}, Unit{}})

def decoding_measure_internal(q: Maybe<&2, B.Number64>, +bs: List<&2, U32>, +ceiling: B.Number64) ->
  Internal(decoding_measure(q, bs, ceiling)):
  match q:
    case None{}: Unit{}
    case Some{+body}: decoding_admitted_internal(C.less_equal64(body, ceiling) && B.octets_all_valid(bs), bs, body, ceiling)

def first_internal(n: Nat, qs: List<&2, Q.Frame>, internal: Internal(qs)) -> Internal(Q.first(n, qs)):
  match n qs:
    case 0n _: Unit{}
    case 1n+k Nil{}: Unit{}
    case 1n+k Con{h, t}:
      match internal:
        case L.Both{head, tail}: L.Both{head, first_internal(k, t, tail)}

law expand_internal:
  for q: Primitive
  Internal(expand(q))
def expand_internal(q):
  match q:
    case Prefix{n, +p}: first_internal(n, expand(p), expand_internal(p))
    case Encode{v}: L.Both{{==}, Unit{}}
    case Decode{+bs, +ceiling}: decoding_measure_internal(B.nat64(B.length(bs)), bs, ceiling)
    case Store{e, +s}: store_bytes_internal(P.encode(D.state_value(s)), e, s)
    case Read{before, cap, received, declared}: L.Both{{==}, Unit{}}

law primitives_only_generate_internal:
  for +xs: List<&2, Primitive>
  Internal(expand_primitives(xs))
def primitives_only_generate_internal(xs):
  match xs:
    case Nil{}: Unit{}
    case Con{+h, t}:
      concatenate_internal(expand(h), expand_primitives(t), expand_internal(h), primitives_only_generate_internal(t))
