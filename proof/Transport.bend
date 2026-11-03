# Private transport preserves exactly both blocks; not a log
# selected to satisfy laws, and does not modify the public protocol.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ../src/Transport.bend as T
import ./Foundations.bend as F
import ./CodecCounters.bend as Q
import ./CodecWordsBE64.bend as E
import ./CodecWordsWord.bend as W
import ./CodecIntegers.bend as I
import ./CodecWordsInverse.bend as J

law word_of_four_blocks:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  {T.word(E.octet(a), E.octet(b), E.octet(c), E.octet(d)) ==
    E.four(a, b, c, d) : U32}
def word_of_four_blocks(a, b, c, d):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      %Equal.sym(Word(32n), Word.mul(32n, E.bits(E.octet(a)), E.bits(16777216)),
        W.zeros_low(24n, 8n, a), W.multiply_power_two(24n, 8n, 32n, E.bits(E.octet(a)))) :
        {U32{Word.add(32n, Word.add(32n, Word.add(32n, _, Word.mul(32n, E.bits(E.octet(b)), E.bits(65536))), Word.mul(32n, E.bits(E.octet(c)), E.bits(256))), E.bits(E.octet(d)))} == E.four(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.mul(32n, E.bits(E.octet(b)), E.bits(65536)),
        W.zeros_low(16n, 16n, W.join(8n, 8n, b, Word.zero(8n))), W.multiply_power_two(16n, 16n, 32n, E.bits(E.octet(b)))) :
        {U32{Word.add(32n, Word.add(32n, Word.add(32n, W.zeros_low(24n, 8n, a), _), Word.mul(32n, E.bits(E.octet(c)), E.bits(256))), E.bits(E.octet(d)))} == E.four(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.mul(32n, E.bits(E.octet(c)), E.bits(256)),
        W.zeros_low(8n, 24n, W.join(8n, 16n, c, Word.zero(16n))), W.multiply_power_two(8n, 24n, 32n, E.bits(E.octet(c)))) :
        {U32{Word.add(32n, Word.add(32n, Word.add(32n, W.zeros_low(24n, 8n, a), W.zeros_low(16n, 16n, W.join(8n, 8n, b, Word.zero(8n)))), _), E.bits(E.octet(d)))} == E.four(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_low(24n, 8n, a), W.join(24n, 8n, W.zeros_low(16n, 8n, b), Word.zero(8n))),
        W.join(24n, 8n, W.zeros_low(16n, 8n, b), a), W.sum_blocks_separate(24n, 8n, W.zeros_low(16n, 8n, b), a)) :
        {U32{Word.add(32n, Word.add(32n, _, W.zeros_low(8n, 24n, W.join(8n, 16n, c, Word.zero(16n)))), E.bits(E.octet(d)))} == E.four(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_low(16n, 16n, W.join(8n, 8n, b, a)), W.join(16n, 16n, W.zeros_low(8n, 8n, c), Word.zero(16n))),
        W.join(16n, 16n, W.zeros_low(8n, 8n, c), W.join(8n, 8n, b, a)), W.sum_blocks_separate(16n, 16n, W.zeros_low(8n, 8n, c), W.join(8n, 8n, b, a))) :
        {U32{Word.add(32n, _, E.bits(E.octet(d)))} == E.four(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_low(8n, 24n, W.join(8n, 16n, c, W.join(8n, 8n, b, a))), E.bits(E.octet(d))),
        W.join(8n, 24n, d, W.join(8n, 16n, c, W.join(8n, 8n, b, a))), W.sum_blocks_separate(8n, 24n, d, W.join(8n, 16n, c, W.join(8n, 8n, b, a)))) :
        {U32{_} == E.four(a, b, c, d) : U32}
      {==}

law header_of_blocks:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +f: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +rest: List<&2, U32>
  {T.header(B.concatenate(B.be64(E.four(a, b, c, d), E.four(e, f, g, h)), rest)) ==
    T.cut(rest, B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)}, Nil{}) : Maybe<&2, T.Parts>}
def header_of_blocks(a, b, c, d, e, f, g, h, rest):
  %Equal.sym(List<&2, U32>, B.be32(E.four(a, b, c, d)),
    [E.octet(a), E.octet(b), E.octet(c), E.octet(d)], E.be32_four(a, b, c, d)) :
    {T.header(B.concatenate(B.concatenate(_, B.be32(E.four(e, f, g, h))), rest)) ==
      T.cut(rest, B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)}, Nil{}) : Maybe<&2, T.Parts>}
  %Equal.sym(List<&2, U32>, B.be32(E.four(e, f, g, h)),
    [E.octet(e), E.octet(f), E.octet(g), E.octet(h)], E.be32_four(e, f, g, h)) :
    {T.header(B.concatenate(B.concatenate([E.octet(a), E.octet(b), E.octet(c), E.octet(d)], _), rest)) ==
      T.cut(rest, B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)}, Nil{}) : Maybe<&2, T.Parts>}
  %Equal.sym(U32, T.word(E.octet(a), E.octet(b), E.octet(c), E.octet(d)), E.four(a, b, c, d), word_of_four_blocks(a, b, c, d)) :
    {T.cut(rest, B.Number64{_, T.word(E.octet(e), E.octet(f), E.octet(g), E.octet(h))}, Nil{}) ==
      T.cut(rest, B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)}, Nil{}) : Maybe<&2, T.Parts>}
  Equal.cong(U32, Maybe<&2, T.Parts>, lo => T.cut(rest, B.Number64{E.four(a, b, c, d), lo}, Nil{}),
    T.word(E.octet(e), E.octet(f), E.octet(g), E.octet(h)), E.four(e, f, g, h), word_of_four_blocks(e, f, g, h))

law header_inverts_be64:
  for +high: U32
  for +low: U32
  for +rest: List<&2, U32>
  {T.header(B.concatenate(B.be64(high, low), rest)) ==
    T.cut(rest, B.Number64{high, low}, Nil{}) : Maybe<&2, T.Parts>}
def header_inverts_be64(high, low, rest):
  match high low:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      header_of_blocks(WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WNil{}}}}}}}}}, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WNil{}}}}}}}}}, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WNil{}}}}}}}}}, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}, rest)

law concatenate_empty:
  for +xs: List<&2, U32>
  {B.concatenate(xs, Nil{}) == xs : List<&2, U32>}
def concatenate_empty(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{h, ys}, B.concatenate(t, Nil{}), t, concatenate_empty(t))

law inversion_accumulated:
  for xs: List<&2, U32>
  for +acc: List<&2, U32>
  for +ys: List<&2, U32>
  {T.invert(T.invert(xs, acc), ys) == T.invert(acc, B.concatenate(xs, ys)) : List<&2, U32>}
def inversion_accumulated(xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      inversion_accumulated(t, Con{h, acc}, ys)

law invert_two_times:
  for +xs: List<&2, U32>
  {T.invert(T.invert(xs, Nil{}), Nil{}) == xs : List<&2, U32>}
def invert_two_times(xs):
  Equal.trans(List<&2, U32>, T.invert(T.invert(xs, Nil{}), Nil{}), B.concatenate(xs, Nil{}), xs,
    inversion_accumulated(xs, Nil{}, Nil{}), concatenate_empty(xs))

law cut_zero:
  for second: List<&2, U32>
  for +acc: List<&2, U32>
  {T.cut(second, B.Number64{0, 0}, acc) ==
    Some{T.Parts{T.invert(acc, Nil{}), second}} : Maybe<&2, T.Parts>}
def cut_zero(second, acc):
  match second:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

law cut_block_of_length_measured:
  for +first: List<&2, U32>
  for +second: List<&2, U32>
  for +number: B.Number64
  for +acc: List<&2, U32>
  for +measured: {B.nat64(B.length(first)) == Some{number} : Maybe<&2, B.Number64>}
  {T.cut(B.concatenate(first, second), number, acc) ==
    Some{T.Parts{T.invert(T.invert(first, acc), Nil{}), second}} : Maybe<&2, T.Parts>}
def cut_block_of_length_measured(first, second, number, acc, measured):
  match first:
    case Nil{}:
      %F.some_injective(B.Number64, B.Number64{0, 0}, number, measured) :
        {T.cut(second, _, acc) == Some{T.Parts{T.invert(acc, Nil{}), second}} : Maybe<&2, T.Parts>}
      cut_zero(second, acc)
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(number), False{}, Q.nat64_successor_never_zero(B.length(t), number, measured)) :
        {T.divert(_, unit => Some{T.Parts{T.invert(acc, Nil{}), Con{h, B.concatenate(t, second)}}},
          unit => T.cut(B.concatenate(t, second), C.decrease64(number), Con{h, acc})) ==
          Some{T.Parts{T.invert(T.invert(t, Con{h, acc}), Nil{}), second}} : Maybe<&2, T.Parts>}
      cut_block_of_length_measured(t, second, C.decrease64(number), Con{h, acc},
        Q.length_of_tail_and_decrement_of_body(h, t, number, measured))

law cut_preserves_exactly_os_two_blocks:
  for +first: List<&2, U32>
  for +second: List<&2, U32>
  for +number: B.Number64
  for measured: {B.nat64(B.length(first)) == Some{number} : Maybe<&2, B.Number64>}
  {T.cut(B.concatenate(first, second), number, Nil{}) ==
    Some{T.Parts{first, second}} : Maybe<&2, T.Parts>}
def cut_preserves_exactly_os_two_blocks(first, second, number, measured):
  Equal.trans(Maybe<&2, T.Parts>, T.cut(B.concatenate(first, second), number, Nil{}),
    Some{T.Parts{T.invert(T.invert(first, Nil{}), Nil{}), second}}, Some{T.Parts{first, second}},
    cut_block_of_length_measured(first, second, number, Nil{}, measured),
    Equal.cong(List<&2, U32>, Maybe<&2, T.Parts>, xs => Some{T.Parts{xs, second}},
      T.invert(T.invert(first, Nil{}), Nil{}), first, invert_two_times(first)))

law separate_be64_and_blocks_all_valid:
  for +first: List<&2, U32>
  for +second: List<&2, U32>
  for number: B.Number64
  for measured: {B.nat64(B.length(first)) == Some{number} : Maybe<&2, B.Number64>}
  for vp: {B.octets_all_valid(first) == True{} : Bool}
  for vs: {B.octets_all_valid(second) == True{} : Bool}
  {T.separate(B.concatenate(F.extract_or(List<&2, U32>, B.number64_bytes(Some{number}), Nil{}), B.concatenate(first, second))) ==
    Some{T.Parts{first, second}} : Maybe<&2, T.Parts>}
def separate_be64_and_blocks_all_valid(first, second, number, measured, vp, vs):
  match number:
    case B.Number64{+high, +low}:
      %Equal.sym(Bool, B.octets_all_valid(B.concatenate(B.be64(high, low), B.concatenate(first, second))), True{},
        I.concatenate_preserves_octets(B.be64(high, low), B.concatenate(first, second),
          I.be64_only_emits_octets(high, low), I.concatenate_preserves_octets(first, second, vp, vs))) :
        {T.validate(_, B.concatenate(B.be64(high, low), B.concatenate(first, second))) == Some{T.Parts{first, second}} : Maybe<&2, T.Parts>}
      Equal.trans(Maybe<&2, T.Parts>, T.header(B.concatenate(B.be64(high, low), B.concatenate(first, second))),
        T.cut(B.concatenate(first, second), B.Number64{high, low}, Nil{}), Some{T.Parts{first, second}},
        header_inverts_be64(high, low, B.concatenate(first, second)),
        cut_preserves_exactly_os_two_blocks(first, second, B.Number64{high, low}, measured))

def separate_assembly_measure(measure: Maybe<&2, B.Number64>,
  +first: List<&2, U32>, +second: List<&2, U32>, -bytes: List<&2, U32>,
  measured: {B.nat64(B.length(first)) == measure : Maybe<&2, B.Number64>},
  assembly: {T.join_combined_header(B.number64_bytes(measure), first, second) == Some{bytes} : Maybe<&2, List<&2, U32>>},
  vp: {B.octets_all_valid(first) == True{} : Bool},
  vs: {B.octets_all_valid(second) == True{} : Bool}) ->
  {T.separate(bytes) == Some{T.Parts{first, second}} : Maybe<&2, T.Parts>}:
  match measure:
    case None{}:
      L.ex_false({T.separate(bytes) == Some{T.Parts{first, second}} : Maybe<&2, T.Parts>},
        F.none_negative_some(List<&2, U32>, bytes, assembly))
    case Some{B.Number64{+high, +low}}:
      %F.some_injective(List<&2, U32>,
        B.concatenate(B.be64(high, low), B.concatenate(first, second)), bytes, assembly) :
        {T.separate(_) == Some{T.Parts{first, second}} : Maybe<&2, T.Parts>}
      separate_be64_and_blocks_all_valid(first, second, B.Number64{high, low}, measured, vp, vs)

# The only external hypotheses are the bytes of both blocks. Representable
# length and exact header follow from Some returned by join.
law separate_inverts_all_assembly_is_valid:
  for +first: List<&2, U32>
  for +second: List<&2, U32>
  for -bytes: List<&2, U32>
  for assembly: {T.join(first, second) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  for vp: {B.octets_all_valid(first) == True{} : Bool}
  for vs: {B.octets_all_valid(second) == True{} : Bool}
  {T.separate(bytes) == Some{T.Parts{first, second}} : Maybe<&2, T.Parts>}
def separate_inverts_all_assembly_is_valid(first, second, bytes, assembly, vp, vs):
  separate_assembly_measure(B.nat64(B.length(first)), first, second, bytes, {==}, assembly, vp, vs)

def first(p: T.Parts) -> List<&2, U32>:
  T.Parts{p1, p2} = p
  p1

def second(p: T.Parts) -> List<&2, U32>:
  T.Parts{p1, p2} = p
  p2

type Cut<-bytes: List<&2, U32>, -number: B.Number64,
  -acc: List<&2, U32>, -parts: T.Parts> is Type:
  Cut{prefix: List<&2, U32>,
    factoring: {bytes == B.concatenate(prefix, second(parts)) : List<&2, U32>},
    assembly: {first(parts) == T.invert(acc, prefix) : List<&2, U32>},
    count: {B.nat64(B.length(prefix)) == Some{number} : Maybe<&2, B.Number64>}}

def zero_cut(+bytes: List<&2, U32>, +number: B.Number64,
  +acc: List<&2, U32>, zero: {C.zero64(number) == True{} : Bool}) ->
  Cut<bytes, number, acc, T.Parts{T.invert(acc, Nil{}), bytes}>:
  Cut{Nil{}, {==}, {==},
    Equal.cong(B.Number64, Maybe<&2, B.Number64>, n => Some{n}, B.Number64{0, 0}, number,
      Equal.sym(B.Number64, number, B.Number64{0, 0}, Q.zero64_only_recognizes_zero(number, zero)))}

def extend_cut(+h: U32, -t: List<&2, U32>, +number: B.Number64,
  -acc: List<&2, U32>, -parts: T.Parts,
  negative_zero: {C.zero64(number) == False{} : Bool},
  cut: Cut<t, C.decrease64(number), Con{h, acc}, parts>) ->
  Cut<Con{h, t}, number, acc, parts>:
  match cut:
    case Cut{+prefix, factoring, assembly, count}:
      Cut{Con{h, prefix},
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{h, xs}, t, B.concatenate(prefix, second(parts)), factoring),
        assembly,
        Equal.trans(Maybe<&2, B.Number64>, B.increment64(B.nat64(B.length(prefix))),
          B.increment64(Some{C.decrease64(number)}), Some{number},
          Equal.cong(Maybe<&2, B.Number64>, Maybe<&2, B.Number64>, n => B.increment64(n),
            B.nat64(B.length(prefix)), Some{C.decrease64(number)}, count),
          Q.increment_inverts_decrease_when_positive(number, negative_zero))}

def invert_cut_empty(zero: Bool, +number: B.Number64, +acc: List<&2, U32>,
  -parts: T.Parts, e: {C.zero64(number) == zero : Bool},
  accepted: {T.empty(zero, acc) == Some{parts} : Maybe<&2, T.Parts>}) ->
  Cut<Nil{}, number, acc, parts>:
  match zero:
    case False{}:
      L.ex_false(Cut<Nil{}, number, acc, parts>, F.none_negative_some(T.Parts, parts, accepted))
    case True{}:
      %F.some_injective(T.Parts, T.Parts{T.invert(acc, Nil{}), Nil{}}, parts, accepted) :
        Cut<Nil{}, number, acc, _>
      zero_cut(Nil{}, number, acc, e)

def invert_cut_deviation(zero: Bool, +h: U32, +t: List<&2, U32>,
  +number: B.Number64, +acc: List<&2, U32>, -parts: T.Parts,
  e: {C.zero64(number) == zero : Bool},
  accepted: {T.divert(zero,
    unit => Some{T.Parts{T.invert(acc, Nil{}), Con{h, t}}},
    unit => T.cut(t, C.decrease64(number), Con{h, acc})) == Some{parts} : Maybe<&2, T.Parts>},
  resume: {T.cut(t, C.decrease64(number), Con{h, acc}) == Some{parts} : Maybe<&2, T.Parts>} ->
    Cut<t, C.decrease64(number), Con{h, acc}, parts>) ->
  Cut<Con{h, t}, number, acc, parts>:
  match zero:
    case False{}:
      extend_cut(h, t, number, acc, parts, e, resume(accepted))
    case True{}:
      %F.some_injective(T.Parts, T.Parts{T.invert(acc, Nil{}), Con{h, t}}, parts, accepted) :
        Cut<Con{h, t}, number, acc, _>
      zero_cut(Con{h, t}, number, acc, e)

# Acceptance alone reconstructs length and consumed prefix.
# The received header is not assumed truthful.
law cut_accepted_has_prefix_and_count_exact:
  for +bytes: List<&2, U32>
  for +number: B.Number64
  for +acc: List<&2, U32>
  for -parts: T.Parts
  for accepted: {T.cut(bytes, number, acc) == Some{parts} : Maybe<&2, T.Parts>}
  Cut<bytes, number, acc, parts>
def cut_accepted_has_prefix_and_count_exact(bytes, number, acc, parts, accepted):
  match bytes:
    case Nil{}:
      invert_cut_empty(C.zero64(number), number, acc, parts, {==}, accepted)
    case Con{+h, +t}:
      invert_cut_deviation(C.zero64(number), h, t, number, acc, parts, {==}, accepted,
        proof => cut_accepted_has_prefix_and_count_exact(t, C.decrease64(number), Con{h, acc}, parts, proof))

law word_of_octets_all_valid:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +va: {U32.is_le(a, 255) == True{} : Bool}
  for +vb: {U32.is_le(b, 255) == True{} : Bool}
  for +vc: {U32.is_le(c, 255) == True{} : Bool}
  for +vd: {U32.is_le(d, 255) == True{} : Bool}
  {T.word(a, b, c, d) == J.assemble(a, b, c, d) : U32}
def word_of_octets_all_valid(a, b, c, d, va, vb, vc, vd):
  %Equal.sym(U32, a, E.octet(J.byte_word(a)), J.octet_valid_reconstituted(a, va)) :
    {T.word(_, b, c, d) == J.assemble(a, b, c, d) : U32}
  %Equal.sym(U32, b, E.octet(J.byte_word(b)), J.octet_valid_reconstituted(b, vb)) :
    {T.word(E.octet(J.byte_word(a)), _, c, d) == J.assemble(a, b, c, d) : U32}
  %Equal.sym(U32, c, E.octet(J.byte_word(c)), J.octet_valid_reconstituted(c, vc)) :
    {T.word(E.octet(J.byte_word(a)), E.octet(J.byte_word(b)), _, d) == J.assemble(a, b, c, d) : U32}
  %Equal.sym(U32, d, E.octet(J.byte_word(d)), J.octet_valid_reconstituted(d, vd)) :
    {T.word(E.octet(J.byte_word(a)), E.octet(J.byte_word(b)), E.octet(J.byte_word(c)), _) == J.assemble(a, b, c, d) : U32}
  word_of_four_blocks(J.byte_word(a), J.byte_word(b), J.byte_word(c), J.byte_word(d))

law header_valid_reconstructs_octets:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +va: {U32.is_le(a, 255) == True{} : Bool}
  for +vb: {U32.is_le(b, 255) == True{} : Bool}
  for +vc: {U32.is_le(c, 255) == True{} : Bool}
  for +vd: {U32.is_le(d, 255) == True{} : Bool}
  for +ve: {U32.is_le(e, 255) == True{} : Bool}
  for +vf: {U32.is_le(f, 255) == True{} : Bool}
  for +vg: {U32.is_le(g, 255) == True{} : Bool}
  for +vh: {U32.is_le(h, 255) == True{} : Bool}
  {B.be64(T.word(a, b, c, d), T.word(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def header_valid_reconstructs_octets(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh):
  %Equal.sym(U32, T.word(a, b, c, d), J.assemble(a, b, c, d), word_of_octets_all_valid(a, b, c, d, va, vb, vc, vd)) :
    {B.be64(_, T.word(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, T.word(e, f, g, h), J.assemble(e, f, g, h), word_of_octets_all_valid(e, f, g, h, ve, vf, vg, vh)) :
    {B.be64(J.assemble(a, b, c, d), _) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
  J.reencode_octets_separate(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh)

def combine_octets_of_tail(-h: U32, -t: List<&2, U32>, -ys: List<&2, U32>,
  head: {U32.is_le(h, 255) == True{} : Bool},
  pair: L.E<{B.octets_all_valid(t) == True{} : Bool}, {B.octets_all_valid(ys) == True{} : Bool}>) ->
  L.E<{B.octets_all_valid(Con{h, t}) == True{} : Bool}, {B.octets_all_valid(ys) == True{} : Bool}>:
  match pair:
    case L.Both{vt, vy}:
      L.Both{F.and_boolean_intro(U32.is_le(h, 255), B.octets_all_valid(t), head, vt), vy}

law separate_octets_of_concatenation:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +all_valid: {B.octets_all_valid(B.concatenate(xs, ys)) == True{} : Bool}
  L.E<{B.octets_all_valid(xs) == True{} : Bool}, {B.octets_all_valid(ys) == True{} : Bool}>
def separate_octets_of_concatenation(xs, ys, all_valid):
  match xs:
    case Nil{}:
      L.Both{{==}, all_valid}
    case Con{+h, +t}:
      combine_octets_of_tail(h, t, ys,
        F.and_boolean_left(U32.is_le(h, 255), B.octets_all_valid(B.concatenate(t, ys)), all_valid),
        separate_octets_of_concatenation(t, ys,
          F.and_boolean_right(U32.is_le(h, 255), B.octets_all_valid(B.concatenate(t, ys)), all_valid)))

def reassemble_cut(+high: U32, +low: U32, +rest: List<&2, U32>,
  -parts: T.Parts, cut: Cut<rest, B.Number64{high, low}, Nil{}, parts>) ->
  {T.join(first(parts), second(parts)) ==
    Some{B.concatenate(B.be64(high, low), rest)} : Maybe<&2, List<&2, U32>>}:
  match cut:
    case Cut{+prefix, factoring, assembly, count}:
      %Equal.sym(List<&2, U32>, first(parts), prefix, assembly) :
        {T.join(_, second(parts)) == Some{B.concatenate(B.be64(high, low), rest)} : Maybe<&2, List<&2, U32>>}
      %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(prefix)), Some{B.Number64{high, low}}, count) :
        {T.join_combined_header(B.number64_bytes(_), prefix, second(parts)) == Some{B.concatenate(B.be64(high, low), rest)} : Maybe<&2, List<&2, U32>>}
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, xs => Some{B.concatenate(B.be64(high, low), xs)},
        B.concatenate(prefix, second(parts)), rest,
        Equal.sym(List<&2, U32>, rest, B.concatenate(prefix, second(parts)), factoring))

def blocks_of_cut_are_octets(-rest: List<&2, U32>, -number: B.Number64,
  +parts: T.Parts, all_valid: {B.octets_all_valid(rest) == True{} : Bool},
  cut: Cut<rest, number, Nil{}, parts>) ->
  L.E<{B.octets_all_valid(first(parts)) == True{} : Bool},
    {B.octets_all_valid(second(parts)) == True{} : Bool}>:
  match cut:
    case Cut{+prefix, factoring, assembly, count}:
      %Equal.sym(List<&2, U32>, first(parts), prefix, assembly) :
        L.E<{B.octets_all_valid(_) == True{} : Bool}, {B.octets_all_valid(second(parts)) == True{} : Bool}>
      separate_octets_of_concatenation(prefix, second(parts),
        (%factoring : {B.octets_all_valid(_) == True{} : Bool}
          all_valid))

def SeparationExact(-bytes: List<&2, U32>, -parts: T.Parts) -> Type:
  L.E<{T.join(first(parts), second(parts)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    L.E<{B.octets_all_valid(first(parts)) == True{} : Bool},
      {B.octets_all_valid(second(parts)) == True{} : Bool}>>

def conclude_cut_faithful(+high: U32, +low: U32, +rest: List<&2, U32>,
  +parts: T.Parts, all_valid: {B.octets_all_valid(rest) == True{} : Bool},
  cut: Cut<rest, B.Number64{high, low}, Nil{}, parts>) ->
  SeparationExact(B.concatenate(B.be64(high, low), rest), parts):
  match cut:
    case Cut{+prefix, +factoring, +assembly, +count}:
      L.Both{reassemble_cut(high, low, rest, parts, Cut{prefix, factoring, assembly, count}),
        blocks_of_cut_are_octets(rest, B.Number64{high, low}, parts, all_valid, Cut{prefix, factoring, assembly, count})}

def header_accepted_reconstituted(
  +a: U32,
  +b: U32,
  +c: U32,
  +d: U32,
  +e: U32,
  +f: U32,
  +g: U32,
  +h: U32,
  +rest: List<&2, U32>, +parts: T.Parts,
  va: {U32.is_le(a, 255) == True{} : Bool},
  vb: {U32.is_le(b, 255) == True{} : Bool},
  vc: {U32.is_le(c, 255) == True{} : Bool},
  vd: {U32.is_le(d, 255) == True{} : Bool},
  ve: {U32.is_le(e, 255) == True{} : Bool},
  vf: {U32.is_le(f, 255) == True{} : Bool},
  vg: {U32.is_le(g, 255) == True{} : Bool},
  vh: {U32.is_le(h, 255) == True{} : Bool},
  vr: {B.octets_all_valid(rest) == True{} : Bool},
  accepted: {T.cut(rest, B.Number64{T.word(a, b, c, d), T.word(e, f, g, h)}, Nil{}) == Some{parts} : Maybe<&2, T.Parts>}) ->
  SeparationExact(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}}}, parts):
  %Equal.cong(List<&2, U32>, List<&2, U32>, xs => B.concatenate(xs, rest),
    B.be64(T.word(a, b, c, d), T.word(e, f, g, h)), [a, b, c, d, e, f, g, h],
    header_valid_reconstructs_octets(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh)) :
    SeparationExact(_, parts)
  conclude_cut_faithful(T.word(a, b, c, d), T.word(e, f, g, h), rest, parts, vr,
    cut_accepted_has_prefix_and_count_exact(rest,
      B.Number64{T.word(a, b, c, d), T.word(e, f, g, h)}, Nil{}, parts, accepted))

def invert_header_accepted(+bytes: List<&2, U32>, +parts: T.Parts,
  +all_valid: {B.octets_all_valid(bytes) == True{} : Bool},
  accepted: {T.header(bytes) == Some{parts} : Maybe<&2, T.Parts>}) ->
  SeparationExact(bytes, parts):
  match bytes:
    case Nil{}:
      L.ex_false(SeparationExact(Nil{}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Nil{}}:
      L.ex_false(SeparationExact(Con{a, Nil{}}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Con{b, Nil{}}}:
      L.ex_false(SeparationExact(Con{a, Con{b, Nil{}}}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Con{b, Con{c, Nil{}}}}:
      L.ex_false(SeparationExact(Con{a, Con{b, Con{c, Nil{}}}}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      L.ex_false(SeparationExact(Con{a, Con{b, Con{c, Con{d, Nil{}}}}}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      L.ex_false(SeparationExact(Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}:
      L.ex_false(SeparationExact(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}:
      L.ex_false(SeparationExact(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}, parts), F.none_negative_some(T.Parts, parts, accepted))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}}}:
      +va = F.and_boolean_left(U32.is_le(a, 255), B.octets_all_valid(Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}}), all_valid)
      +tail1 = F.and_boolean_right(U32.is_le(a, 255), B.octets_all_valid(Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}}), all_valid)
      +vb = F.and_boolean_left(U32.is_le(b, 255), B.octets_all_valid(Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}), tail1)
      +tail2 = F.and_boolean_right(U32.is_le(b, 255), B.octets_all_valid(Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}), tail1)
      +vc = F.and_boolean_left(U32.is_le(c, 255), B.octets_all_valid(Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}), tail2)
      +tail3 = F.and_boolean_right(U32.is_le(c, 255), B.octets_all_valid(Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}), tail2)
      +vd = F.and_boolean_left(U32.is_le(d, 255), B.octets_all_valid(Con{e, Con{f, Con{g, Con{h, rest}}}}), tail3)
      +tail4 = F.and_boolean_right(U32.is_le(d, 255), B.octets_all_valid(Con{e, Con{f, Con{g, Con{h, rest}}}}), tail3)
      +ve = F.and_boolean_left(U32.is_le(e, 255), B.octets_all_valid(Con{f, Con{g, Con{h, rest}}}), tail4)
      +tail5 = F.and_boolean_right(U32.is_le(e, 255), B.octets_all_valid(Con{f, Con{g, Con{h, rest}}}), tail4)
      +vf = F.and_boolean_left(U32.is_le(f, 255), B.octets_all_valid(Con{g, Con{h, rest}}), tail5)
      +tail6 = F.and_boolean_right(U32.is_le(f, 255), B.octets_all_valid(Con{g, Con{h, rest}}), tail5)
      +vg = F.and_boolean_left(U32.is_le(g, 255), B.octets_all_valid(Con{h, rest}), tail6)
      +tail7 = F.and_boolean_right(U32.is_le(g, 255), B.octets_all_valid(Con{h, rest}), tail6)
      +vh = F.and_boolean_left(U32.is_le(h, 255), B.octets_all_valid(rest), tail7)
      +tail8 = F.and_boolean_right(U32.is_le(h, 255), B.octets_all_valid(rest), tail7)
      header_accepted_reconstituted(a, b, c, d, e, f, g, h, rest, parts,
        va, vb, vc, vd, ve, vf, vg, vh, tail8, accepted)

def invert_validation_accepts(ok: Bool, +bytes: List<&2, U32>, +parts: T.Parts,
  all_valid: {B.octets_all_valid(bytes) == ok : Bool},
  accepted: {T.validate(ok, bytes) == Some{parts} : Maybe<&2, T.Parts>}) ->
  SeparationExact(bytes, parts):
  match ok:
    case False{}:
      L.ex_false(SeparationExact(bytes, parts), F.none_negative_some(T.Parts, parts, accepted))
    case True{}:
      invert_header_accepted(bytes, parts, all_valid, accepted)

law all_separation_accepts_reconstructs_packet_original:
  for +bytes: List<&2, U32>
  for +parts: T.Parts
  for accepted: {T.separate(bytes) == Some{parts} : Maybe<&2, T.Parts>}
  SeparationExact(bytes, parts)
def all_separation_accepts_reconstructs_packet_original(bytes, parts, accepted):
  invert_validation_accepts(B.octets_all_valid(bytes), bytes, parts, {==}, accepted)
