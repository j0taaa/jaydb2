# Invert ANY accepted input. Induction follows the original list
# byte by byte; Prefix stores only the still-incomplete scalar section.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./CodecUTF8.bend as T
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InverseBits.bend as I
import ./CodecUTF8Inverse.bend as E
import ./CodecUTF8InverseCanonical.bend as K
import ./CodecWordsWord.bend as W
import ./Foundations.bend as F

type Prefix is Data:
  Free{}
  Two{hi: Word(5n)}
  Three1{hi: Word(4n)}
  Three2{hi: Word(4n), b0: Word(6n)}
  Four1{hi: Word(3n)}
  Four2{hi: Word(3n), b0: Word(6n)}
  Four3{hi: Word(3n), b0: Word(6n), b1: Word(6n)}

def start2(hi: Word(5n)) -> U32:
  U32{W.join(5n, 27n, hi, Word.zero(27n))}

def start3(hi: Word(4n)) -> U32:
  U32{W.join(4n, 28n, hi, Word.zero(28n))}

def start4(hi: Word(3n)) -> U32:
  U32{W.join(3n, 29n, hi, Word.zero(29n))}

def unicode(p: Prefix) -> C.Unicode:
  match p:
    case Free{}:
      C.Start{}
    case Two{hi}:
      C.Continue{1n, start2(hi), 128}
    case Three1{hi}:
      C.Continue{2n, start3(hi), 2048}
    case Three2{hi, b0}:
      C.Continue{1n, E.accumulate(start3(hi), b0), 2048}
    case Four1{hi}:
      C.Continue{3n, start4(hi), 65536}
    case Four2{hi, b0}:
      C.Continue{2n, E.accumulate(start4(hi), b0), 65536}
    case Four3{hi, b0, b1}:
      C.Continue{1n, E.accumulate(E.accumulate(start4(hi), b0), b1), 65536}

def pending(p: Prefix) -> List<&2, U32>:
  match p:
    case Free{}:
      []
    case Two{hi}:
      [I.prefix2(hi)]
    case Three1{hi}:
      [I.prefix3(hi)]
    case Three2{hi, b0}:
      [I.prefix3(hi), X.continuation(b0)]
    case Four1{hi}:
      [I.prefix4(hi)]
    case Four2{hi, b0}:
      [I.prefix4(hi), X.continuation(b0)]
    case Four3{hi, b0, b1}:
      [I.prefix4(hi), X.continuation(b0), X.continuation(b1)]

def Pending(p: Prefix) -> Type:
  match p:
    case Free{}:
      Empty
    case _:
      Unit

def remaining(p: Prefix, bs: List<&2, U32>) -> List<&2, U32>:
  B.concatenate(pending(p), bs)

def encode_accumulated(acc: String, bs: List<&2, U32>) -> List<&2, U32>:
  match acc:
    case SNil{}:
      bs
    case SCon{Chr{cp}, tail}:
      encode_accumulated(tail, B.concatenate(B.utf8_code(cp), bs))

def Accepts(bs: List<&2, U32>, t: T.TextValue, s: String) -> Type:
  {T.finalize_text(T.traverse_text(bs, t)) == Some{s} : Maybe<&2, String>}

def Inverts(bs: List<&2, U32>, p: Prefix, acc: String, s: String) -> Type:
  {B.utf8(s) == encode_accumulated(acc, remaining(p, bs)) : List<&2, U32>}

def Suffix(bs: List<&2, U32>) -> Type:
  @p: Prefix -> @acc: String -> @s: String ->
  Accepts(bs, T.Reading{unicode(p), acc}, s) -> Inverts(bs, p, acc, s)

def Step(p: Prefix, b: U32, tail: List<&2, U32>, acc: String, s: String) -> Type:
  Accepts(tail, T.step_text(T.Reading{unicode(p), acc}, b), s) -> Inverts(Con{b, tail}, p, acc, s)

law utf8_reverse_accumulated:
  for +s: String
  for +acc: String
  {B.utf8(String.reverse.go(s, acc)) == encode_accumulated(s, B.utf8(acc)) : List<&2, U32>}
def utf8_reverse_accumulated(s, acc):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{cp}, tail}:
      utf8_reverse_accumulated(tail, SCon{Chr{cp}, acc})

law traverse_invalid:
  for +bs: List<&2, U32>
  {T.traverse_text(bs, T.TextInvalid{}) == T.TextInvalid{} : T.TextValue}
def traverse_invalid(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, tail}:
      traverse_invalid(tail)

def invalid_negative_accepts(-A: Type, +bs: List<&2, U32>, -s: String, accepted: Accepts(bs, T.TextInvalid{}, s)) -> A:
  L.ex_false(A, F.none_negative_some(String, s,
    (%traverse_invalid(bs) : {T.finalize_text(_) == Some{s} : Maybe<&2, String>} accepted)))

law end_inverts:
  for +p: Prefix
  for +acc: String
  for +s: String
  for accepted: Accepts([], T.Reading{unicode(p), acc}, s)
  Inverts([], p, acc, s)
def end_inverts(p, acc, s, accepted):
  match p:
    case Free{}:
      Equal.trans(List<&2, U32>, B.utf8(s), B.utf8(String.reverse(acc)), encode_accumulated(acc, []),
        Equal.cong(String, List<&2, U32>, z => B.utf8(z), s, String.reverse(acc),
          Equal.sym(String, String.reverse(acc), s, F.some_injective(String, String.reverse(acc), s, accepted))),
        utf8_reverse_accumulated(acc, ""))
    case Two{hi}:
      L.ex_false(Inverts([], p, acc, s), F.none_negative_some(String, s, accepted))
    case Three1{hi}:
      L.ex_false(Inverts([], p, acc, s), F.none_negative_some(String, s, accepted))
    case Three2{hi, b0}:
      L.ex_false(Inverts([], p, acc, s), F.none_negative_some(String, s, accepted))
    case Four1{hi}:
      L.ex_false(Inverts([], p, acc, s), F.none_negative_some(String, s, accepted))
    case Four2{hi, b0}:
      L.ex_false(Inverts([], p, acc, s), F.none_negative_some(String, s, accepted))
    case Four3{hi, b0, b1}:
      L.ex_false(Inverts([], p, acc, s), F.none_negative_some(String, s, accepted))

law character_inverts:
  for +cp: U32
  for +bytes: List<&2, U32>
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for ih: Suffix(tail)
  for reencodes: {B.utf8_code(cp) == bytes : List<&2, U32>}
  for accepted: Accepts(tail, T.Reading{C.Start{}, SCon{Chr{cp}, acc}}, s)
  {B.utf8(s) == encode_accumulated(acc, B.concatenate(bytes, tail)) : List<&2, U32>}
def character_inverts(cp, bytes, tail, acc, s, ih, reencodes, accepted):
  %reencodes : {B.utf8(s) == encode_accumulated(acc, B.concatenate(_, tail)) : List<&2, U32>}
  ih(Free{}, SCon{Chr{cp}, acc}, s, accepted)

law checked_inverts:
  for ok: Bool
  for +cp: U32
  for +bytes: List<&2, U32>
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for ih: Suffix(tail)
  for reencodes: {ok == True{} : Bool} -> {B.utf8_code(cp) == bytes : List<&2, U32>}
  for accepted: Accepts(tail, T.join(C.scalar_checked(ok, cp), acc), s)
  {B.utf8(s) == encode_accumulated(acc, B.concatenate(bytes, tail)) : List<&2, U32>}
def checked_inverts(ok, cp, bytes, tail, acc, s, ih, reencodes, accepted):
  match ok:
    case False{}:
      invalid_negative_accepts({B.utf8(s) == encode_accumulated(acc, B.concatenate(bytes, tail)) : List<&2, U32>}, tail, s, accepted)
    case True{}:
      character_inverts(cp, bytes, tail, acc, s, ih, reencodes({==}), accepted)

def InitialPartial(n: Nat, base: U32, minimum: U32, b: U32, tail: List<&2, U32>, acc: String, s: String) -> Type:
  Accepts(tail, T.Reading{C.Continue{n, (b - base : U32), minimum}, acc}, s) ->
  {B.utf8(s) == encode_accumulated(acc, Con{b, tail}) : List<&2, U32>}

law initial2_inverts:
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for form: {b == I.prefix2(W.adjust(5n, 32n, X.bits(b))) : U32}
  for ih: Suffix(tail)
  InitialPartial(1n, 192, 128, b, tail, acc, s)
def initial2_inverts(b, tail, acc, s, form, ih):
  %Equal.sym(U32, b, I.prefix2(W.adjust(5n, 32n, X.bits(b))), form) : InitialPartial(1n, 192, 128, _, tail, acc, s)
  accepted => ih(Two{W.adjust(5n, 32n, X.bits(b))}, acc, s,
    %I.prefix2_subtract(W.adjust(5n, 32n, X.bits(b))) : Accepts(tail, T.Reading{C.Continue{1n, _, 128}, acc}, s)
    accepted)

law initial3_inverts:
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for form: {b == I.prefix3(W.adjust(4n, 32n, X.bits(b))) : U32}
  for ih: Suffix(tail)
  InitialPartial(2n, 224, 2048, b, tail, acc, s)
def initial3_inverts(b, tail, acc, s, form, ih):
  %Equal.sym(U32, b, I.prefix3(W.adjust(4n, 32n, X.bits(b))), form) : InitialPartial(2n, 224, 2048, _, tail, acc, s)
  accepted => ih(Three1{W.adjust(4n, 32n, X.bits(b))}, acc, s,
    %I.prefix3_subtract(W.adjust(4n, 32n, X.bits(b))) : Accepts(tail, T.Reading{C.Continue{2n, _, 2048}, acc}, s)
    accepted)

law initial4_inverts:
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for form: {b == I.prefix4(W.adjust(3n, 32n, X.bits(b))) : U32}
  for ih: Suffix(tail)
  InitialPartial(3n, 240, 65536, b, tail, acc, s)
def initial4_inverts(b, tail, acc, s, form, ih):
  %Equal.sym(U32, b, I.prefix4(W.adjust(3n, 32n, X.bits(b))), form) : InitialPartial(3n, 240, 65536, _, tail, acc, s)
  accepted => ih(Four1{W.adjust(3n, 32n, X.bits(b))}, acc, s,
    %I.prefix4_subtract(W.adjust(3n, 32n, X.bits(b))) : Accepts(tail, T.Reading{C.Continue{3n, _, 65536}, acc}, s)
    accepted)

law start_inverts:
  for ascii: Bool
  for two: Bool
  for three: Bool
  for four: Bool
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for a: {U32.is_lt(b, 128) == ascii : Bool}
  for +d: {U32.is_ge(b, 194) && U32.is_le(b, 223) == two : Bool}
  for +t: {U32.is_ge(b, 224) && U32.is_le(b, 239) == three : Bool}
  for +q: {U32.is_ge(b, 240) && U32.is_le(b, 244) == four : Bool}
  for ih: Suffix(tail)
  for accepted: Accepts(tail, T.join(C.start_utf8(ascii, two, three, four, b), acc), s)
  Inverts(Con{b, tail}, Free{}, acc, s)
def start_inverts(ascii, two, three, four, b, tail, acc, s, a, d, t, q, ih, accepted):
  match ascii two three four:
    case True{} _ _ _:
      character_inverts(b, [b], tail, acc, s, ih, K.ascii_reencodes(b, a), accepted)
    case False{} True{} _ _:
      proof = initial2_inverts(b, tail, acc, s,
        K.prefix2_reconstituted(b, F.and_boolean_left(U32.is_ge(b, 194), U32.is_le(b, 223), d), F.and_boolean_right(U32.is_ge(b, 194), U32.is_le(b, 223), d)), ih)
      proof(accepted)
    case False{} False{} True{} _:
      proof = initial3_inverts(b, tail, acc, s,
        K.prefix3_reconstituted(b, F.and_boolean_left(U32.is_ge(b, 224), U32.is_le(b, 239), t), F.and_boolean_right(U32.is_ge(b, 224), U32.is_le(b, 239), t)), ih)
      proof(accepted)
    case False{} False{} False{} True{}:
      proof = initial4_inverts(b, tail, acc, s,
        K.prefix4_reconstituted(b, F.and_boolean_left(U32.is_ge(b, 240), U32.is_le(b, 244), q), F.and_boolean_right(U32.is_ge(b, 240), U32.is_le(b, 244), q)), ih)
      proof(accepted)
    case False{} False{} False{} False{}:
      invalid_negative_accepts(Inverts(Con{b, tail}, Free{}, acc, s), tail, s, accepted)

# One continuation step, for all reachable partial states.
law continuation_normal_inverts:
  for +p: Prefix
  for +lo: Word(6n)
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for pending: Pending(p)
  for ih: Suffix(tail)
  Step(p, X.continuation(lo), tail, acc, s)
def continuation_normal_inverts(p, lo, tail, acc, s, pending, ih):
  match p:
    case Free{}:
      L.ex_false(Step(Free{}, X.continuation(lo), tail, acc, s), pending)
    case Two{hi}:
      match hi lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Scalar, C.step_utf8(unicode(Two{hi}), X.continuation(lo)), C.complete_utf8(0n, X.scalar2(hi, lo), 128), I.step_continuation(0n, start2(hi), 128, lo)) :
            Accepts(tail, T.join(_, acc), s) -> Inverts(Con{X.continuation(lo), tail}, Two{hi}, acc, s)
          accepted => checked_inverts(U32.is_ge(X.scalar2(hi, lo), 128) && B.code_valid(X.scalar2(hi, lo)), X.scalar2(hi, lo), [I.prefix2(hi), X.continuation(lo)], tail, acc, s, ih,
            e => K.form2_reencodes(hi, lo, F.and_boolean_left(U32.is_ge(X.scalar2(hi, lo), 128), B.code_valid(X.scalar2(hi, lo)), e)), accepted)
    case Three1{hi}:
      match hi lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Scalar, C.step_utf8(unicode(Three1{hi}), X.continuation(lo)), C.complete_utf8(1n, E.accumulate(start3(hi), lo), 2048), I.step_continuation(1n, start3(hi), 2048, lo)) :
            Accepts(tail, T.join(_, acc), s) -> Inverts(Con{X.continuation(lo), tail}, Three1{hi}, acc, s)
          accepted => ih(Three2{hi, lo}, acc, s, accepted)
    case Three2{hi, b0}:
      match hi b0 lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Scalar, C.step_utf8(unicode(Three2{hi, b0}), X.continuation(lo)), C.complete_utf8(0n, X.scalar3(hi, b0, lo), 2048), I.step_continuation(0n, E.accumulate(start3(hi), b0), 2048, lo)) :
            Accepts(tail, T.join(_, acc), s) -> Inverts(Con{X.continuation(lo), tail}, Three2{hi, b0}, acc, s)
          accepted => checked_inverts(U32.is_ge(X.scalar3(hi, b0, lo), 2048) && B.code_valid(X.scalar3(hi, b0, lo)), X.scalar3(hi, b0, lo), [I.prefix3(hi), X.continuation(b0), X.continuation(lo)], tail, acc, s, ih,
            e => K.form3_reencodes(hi, b0, lo, F.and_boolean_left(U32.is_ge(X.scalar3(hi, b0, lo), 2048), B.code_valid(X.scalar3(hi, b0, lo)), e)), accepted)
    case Four1{hi}:
      match hi lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Scalar, C.step_utf8(unicode(Four1{hi}), X.continuation(lo)), C.complete_utf8(2n, E.accumulate(start4(hi), lo), 65536), I.step_continuation(2n, start4(hi), 65536, lo)) :
            Accepts(tail, T.join(_, acc), s) -> Inverts(Con{X.continuation(lo), tail}, Four1{hi}, acc, s)
          accepted => ih(Four2{hi, lo}, acc, s, accepted)
    case Four2{hi, b0}:
      match hi b0 lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Scalar, C.step_utf8(unicode(Four2{hi, b0}), X.continuation(lo)), C.complete_utf8(1n, E.accumulate(E.accumulate(start4(hi), b0), lo), 65536), I.step_continuation(1n, E.accumulate(start4(hi), b0), 65536, lo)) :
            Accepts(tail, T.join(_, acc), s) -> Inverts(Con{X.continuation(lo), tail}, Four2{hi, b0}, acc, s)
          accepted => ih(Four3{hi, b0, lo}, acc, s, accepted)
    case Four3{hi, b0, b1}:
      match hi b0 b1 lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Scalar, C.step_utf8(unicode(Four3{hi, b0, b1}), X.continuation(lo)), C.complete_utf8(0n, X.scalar4(hi, b0, b1, lo), 65536), I.step_continuation(0n, E.accumulate(E.accumulate(start4(hi), b0), b1), 65536, lo)) :
            Accepts(tail, T.join(_, acc), s) -> Inverts(Con{X.continuation(lo), tail}, Four3{hi, b0, b1}, acc, s)
          accepted => checked_inverts(U32.is_ge(X.scalar4(hi, b0, b1, lo), 65536) && B.code_valid(X.scalar4(hi, b0, b1, lo)), X.scalar4(hi, b0, b1, lo), [I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(lo)], tail, acc, s, ih,
            e => K.form4_reencodes(hi, b0, b1, lo, F.and_boolean_left(U32.is_ge(X.scalar4(hi, b0, b1, lo), 65536), B.code_valid(X.scalar4(hi, b0, b1, lo)), e)), accepted)

# Continuation-byte rejection is independent of counter and payload.
def continuation_rejected(+n: Nat, +cp: U32, +minimum: U32, +b: U32,
  e: {U32.is_ge(b, 128) && U32.is_le(b, 191) == False{} : Bool}) ->
  {C.resume_utf8(U32.is_ge(b, 128) && U32.is_le(b, 191), n, cp, minimum, b) == C.UTFInvalid{} : C.Scalar}:
  %Equal.sym(Bool, U32.is_ge(b, 128) && U32.is_le(b, 191), False{}, e) :
    {C.resume_utf8(_, n, cp, minimum, b) == C.UTFInvalid{} : C.Scalar}
  {==}

law step_pending_rejected:
  for +p: Prefix
  for +b: U32
  for pending: Pending(p)
  for e: {U32.is_ge(b, 128) && U32.is_le(b, 191) == False{} : Bool}
  {C.step_utf8(unicode(p), b) == C.UTFInvalid{} : C.Scalar}
def step_pending_rejected(p, b, pending, e):
  match p:
    case Free{}:
      L.ex_false({C.step_utf8(C.Start{}, b) == C.UTFInvalid{} : C.Scalar}, pending)
    case Two{hi}:
      continuation_rejected(0n, start2(hi), 128, b, e)
    case Three1{hi}:
      continuation_rejected(1n, start3(hi), 2048, b, e)
    case Three2{hi, b0}:
      continuation_rejected(0n, E.accumulate(start3(hi), b0), 2048, b, e)
    case Four1{hi}:
      continuation_rejected(2n, start4(hi), 65536, b, e)
    case Four2{hi, b0}:
      continuation_rejected(1n, E.accumulate(start4(hi), b0), 65536, b, e)
    case Four3{hi, b0, b1}:
      continuation_rejected(0n, E.accumulate(E.accumulate(start4(hi), b0), b1), 65536, b, e)

law step_pending_cases:
  for ok: Bool
  for +p: Prefix
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for pending: Pending(p)
  for +e: {U32.is_ge(b, 128) && U32.is_le(b, 191) == ok : Bool}
  for ih: Suffix(tail)
  Step(p, b, tail, acc, s)
def step_pending_cases(ok, p, b, tail, acc, s, pending, e, ih):
  match ok:
    case False{}:
      %Equal.sym(C.Scalar, C.step_utf8(unicode(p), b), C.UTFInvalid{}, step_pending_rejected(p, b, pending, e)) :
        Accepts(tail, T.join(_, acc), s) -> Inverts(Con{b, tail}, p, acc, s)
      accepted => invalid_negative_accepts(Inverts(Con{b, tail}, p, acc, s), tail, s, accepted)
    case True{}:
      form = K.continuation_reconstituted(b,
        F.and_boolean_left(U32.is_ge(b, 128), U32.is_le(b, 191), e),
        F.and_boolean_right(U32.is_ge(b, 128), U32.is_le(b, 191), e))
      %Equal.sym(U32, b, X.continuation(E.lo6(b)), form) : Step(p, _, tail, acc, s)
      continuation_normal_inverts(p, E.lo6(b), tail, acc, s, pending, ih)

law step_inverts:
  for +p: Prefix
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for ih: Suffix(tail)
  Step(p, b, tail, acc, s)
def step_inverts(p, b, tail, acc, s, ih):
  match p:
    case Free{}:
      accepted => start_inverts(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244),
        b, tail, acc, s, {==}, {==}, {==}, {==}, ih, accepted)
    case Two{hi}:
      step_pending_cases(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Three1{hi}:
      step_pending_cases(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Three2{hi, b0}:
      step_pending_cases(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Four1{hi}:
      step_pending_cases(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Four2{hi, b0}:
      step_pending_cases(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Four3{hi, b0, b1}:
      step_pending_cases(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)

# The induction hypothesis applies strictly to tail; there is no
# canonicity, segmentation, octets_all_valid or roundtrip premise.
law all_os_suffixes_invert:
  for +bs: List<&2, U32>
  Suffix(bs)
def all_os_suffixes_invert(bs):
  match bs:
    case Nil{}:
      p => acc => s => accepted => end_inverts(p, acc, s, accepted)
    case Con{+b, +tail}:
      ih = all_os_suffixes_invert(tail)
      p => acc => s => accepted =>
        proof = step_inverts(p, b, tail, acc, s, ih)
        proof(accepted)

# General reverse direction: for every accepted list, original reencoding
# returns EXACTLY the same U32 values, in the same order without truncation.
law utf8_input_accepts_reencodes_exactly:
  for +bs: List<&2, U32>
  for +s: String
  for accepted: {T.finalize_text(T.traverse_text(bs, T.Reading{C.Start{}, ""})) == Some{s} : Maybe<&2, String>}
  {B.utf8(s) == bs : List<&2, U32>}
def utf8_input_accepts_reencodes_exactly(bs, s, accepted):
  proof = all_os_suffixes_invert(bs)
  proof(Free{}, "", s, accepted)

law concatenate_empty_right:
  for +bs: List<&2, U32>
  {B.concatenate(bs, []) == bs : List<&2, U32>}
def concatenate_empty_right(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, tail}:
      Equal.cong(List<&2, U32>, List<&2, U32>, r => Con{b, r}, B.concatenate(tail, []), tail, concatenate_empty_right(tail))

# In particular covers every 1-, 2-, 3- or 4-byte sequence emitting one
# scalar. The list is arbitrary; even its length is not assumed.
law utf8_sequence_scalar_accepts_reencodes_exactly:
  for +bs: List<&2, U32>
  for +cp: U32
  for accepted: {T.finalize_text(T.traverse_text(bs, T.Reading{C.Start{}, ""})) == Some{SCon{Chr{cp}, ""}} : Maybe<&2, String>}
  {B.utf8_code(cp) == bs : List<&2, U32>}
def utf8_sequence_scalar_accepts_reencodes_exactly(bs, cp, accepted):
  Equal.trans(List<&2, U32>, B.utf8_code(cp), B.utf8(SCon{Chr{cp}, ""}), bs,
    Equal.sym(List<&2, U32>, B.concatenate(B.utf8_code(cp), []), B.utf8_code(cp), concatenate_empty_right(B.utf8_code(cp))),
    utf8_input_accepts_reencodes_exactly(bs, SCon{Chr{cp}, ""}, accepted))
