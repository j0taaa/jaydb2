# Scalar inversion of the original encoder by actual parser transduction.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecUTF8.bend as T
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InverseBits.bend as I
import ./CodecWordsWord.bend as W
import ./CodecUnicode.bend as U
import ./Foundations.bend as F

def accumulate(cp: U32, lo: Word(6n)) -> U32:
  U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, X.bits(cp)))}

law traverse_ascii:
  for +cp: U32
  for +acc: String
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {T.traverse_text([cp], T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{cp}, acc}} : T.TextValue}
def traverse_ascii(cp, acc, ascii):
  %Equal.sym(Bool, U32.is_lt(cp, 128), True{}, ascii) :
    {T.join(C.start_utf8(_, U32.is_ge(cp, 194) && U32.is_le(cp, 223), U32.is_ge(cp, 224) && U32.is_le(cp, 239), U32.is_ge(cp, 240) && U32.is_le(cp, 244), cp), acc) == T.Reading{C.Start{}, SCon{Chr{cp}, acc}} : T.TextValue}
  {==}

law traverse_form2:
  for +hi: Word(5n)
  for +b0: Word(6n)
  for +acc: String
  for +minimum: {U32.is_ge(X.scalar2(hi, b0), 128) == True{} : Bool}
  for +valid: {B.code_valid(X.scalar2(hi, b0)) == True{} : Bool}
  {T.traverse_text([I.prefix2(hi), X.continuation(b0)], T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar2(hi, b0)}, acc}} : T.TextValue}
def traverse_form2(hi, b0, acc, minimum, valid):
  match hi b0:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}}:
      %Equal.sym(C.Scalar, C.step_utf8(C.Start{}, I.prefix2(hi)), C.Partial{C.Continue{1n, U32{W.join(5n, 27n, hi, Word.zero(27n))}, 128}}, I.start_two(hi, b0, minimum)) :
        {T.traverse_text([X.continuation(b0)], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar2(hi, b0)}, acc}} : T.TextValue}
      %Equal.sym(C.Scalar, C.step_utf8(C.Continue{1n, U32{W.join(5n, 27n, hi, Word.zero(27n))}, 128}, X.continuation(b0)), C.complete_utf8(0n, accumulate(U32{W.join(5n, 27n, hi, Word.zero(27n))}, b0), 128), I.step_continuation(0n, U32{W.join(5n, 27n, hi, Word.zero(27n))}, 128, b0)) :
        {T.traverse_text([], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar2(hi, b0)}, acc}} : T.TextValue}
      %Equal.sym(Bool, U32.is_ge(X.scalar2(hi, b0), 128) && B.code_valid(X.scalar2(hi, b0)), True{}, F.and_boolean_intro(U32.is_ge(X.scalar2(hi, b0), 128), B.code_valid(X.scalar2(hi, b0)), minimum, valid)) :
        {T.join(C.scalar_checked(_, X.scalar2(hi, b0)), acc) == T.Reading{C.Start{}, SCon{Chr{X.scalar2(hi, b0)}, acc}} : T.TextValue}
      {==}

law traverse_form3:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +acc: String
  for +minimum: {U32.is_ge(X.scalar3(hi, b0, b1), 2048) == True{} : Bool}
  for +valid: {B.code_valid(X.scalar3(hi, b0, b1)) == True{} : Bool}
  {T.traverse_text([I.prefix3(hi), X.continuation(b0), X.continuation(b1)], T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar3(hi, b0, b1)}, acc}} : T.TextValue}
def traverse_form3(hi, b0, b1, acc, minimum, valid):
  match hi b0 b1:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}}:
      %Equal.sym(C.Scalar, C.step_utf8(C.Start{}, I.prefix3(hi)), C.Partial{C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}}, I.start_three(hi)) :
        {T.traverse_text([X.continuation(b0), X.continuation(b1)], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar3(hi, b0, b1)}, acc}} : T.TextValue}
      %Equal.sym(C.Scalar, C.step_utf8(C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}, X.continuation(b0)), C.complete_utf8(1n, accumulate(U32{W.join(4n, 28n, hi, Word.zero(28n))}, b0), 2048), I.step_continuation(1n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048, b0)) :
        {T.traverse_text([X.continuation(b1)], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar3(hi, b0, b1)}, acc}} : T.TextValue}
      %Equal.sym(C.Scalar, C.step_utf8(C.Continue{1n, accumulate(U32{W.join(4n, 28n, hi, Word.zero(28n))}, b0), 2048}, X.continuation(b1)), C.complete_utf8(0n, accumulate(accumulate(U32{W.join(4n, 28n, hi, Word.zero(28n))}, b0), b1), 2048), I.step_continuation(0n, accumulate(U32{W.join(4n, 28n, hi, Word.zero(28n))}, b0), 2048, b1)) :
        {T.traverse_text([], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar3(hi, b0, b1)}, acc}} : T.TextValue}
      %Equal.sym(Bool, U32.is_ge(X.scalar3(hi, b0, b1), 2048) && B.code_valid(X.scalar3(hi, b0, b1)), True{}, F.and_boolean_intro(U32.is_ge(X.scalar3(hi, b0, b1), 2048), B.code_valid(X.scalar3(hi, b0, b1)), minimum, valid)) :
        {T.join(C.scalar_checked(_, X.scalar3(hi, b0, b1)), acc) == T.Reading{C.Start{}, SCon{Chr{X.scalar3(hi, b0, b1)}, acc}} : T.TextValue}
      {==}

law traverse_form4:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for +acc: String
  for +minimum: {U32.is_ge(X.scalar4(hi, b0, b1, b2), 65536) == True{} : Bool}
  for +valid: {B.code_valid(X.scalar4(hi, b0, b1, b2)) == True{} : Bool}
  {T.traverse_text([I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(b2)], T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
def traverse_form4(hi, b0, b1, b2, acc, minimum, valid):
  match hi b0 b1 b2:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WNil{}}}}}}}:
      %Equal.sym(C.Scalar, C.step_utf8(C.Start{}, I.prefix4(hi)), C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}}, I.start_four(hi, I.scalar4_prefix_bounded(hi, b0, b1, b2, valid))) :
        {T.traverse_text([X.continuation(b0), X.continuation(b1), X.continuation(b2)], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
      %Equal.sym(C.Scalar, C.step_utf8(C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}, X.continuation(b0)), C.complete_utf8(2n, accumulate(U32{W.join(3n, 29n, hi, Word.zero(29n))}, b0), 65536), I.step_continuation(2n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536, b0)) :
        {T.traverse_text([X.continuation(b1), X.continuation(b2)], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
      %Equal.sym(C.Scalar, C.step_utf8(C.Continue{2n, accumulate(U32{W.join(3n, 29n, hi, Word.zero(29n))}, b0), 65536}, X.continuation(b1)), C.complete_utf8(1n, accumulate(accumulate(U32{W.join(3n, 29n, hi, Word.zero(29n))}, b0), b1), 65536), I.step_continuation(1n, accumulate(U32{W.join(3n, 29n, hi, Word.zero(29n))}, b0), 65536, b1)) :
        {T.traverse_text([X.continuation(b2)], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
      %Equal.sym(C.Scalar, C.step_utf8(C.Continue{1n, accumulate(accumulate(U32{W.join(3n, 29n, hi, Word.zero(29n))}, b0), b1), 65536}, X.continuation(b2)), C.complete_utf8(0n, accumulate(accumulate(accumulate(U32{W.join(3n, 29n, hi, Word.zero(29n))}, b0), b1), b2), 65536), I.step_continuation(0n, accumulate(accumulate(U32{W.join(3n, 29n, hi, Word.zero(29n))}, b0), b1), 65536, b2)) :
        {T.traverse_text([], T.join(_, acc)) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
      %Equal.sym(Bool, U32.is_ge(X.scalar4(hi, b0, b1, b2), 65536) && B.code_valid(X.scalar4(hi, b0, b1, b2)), True{}, F.and_boolean_intro(U32.is_ge(X.scalar4(hi, b0, b1, b2), 65536), B.code_valid(X.scalar4(hi, b0, b1, b2)), minimum, valid)) :
        {T.join(C.scalar_checked(_, X.scalar4(hi, b0, b1, b2)), acc) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
      {==}

# Transports only a Boolean fact, never the inversion conclusion.
def fact_transferred(-P: U32 -> Bool, -a: U32, -b: U32,
  e: {a == b : U32}, fact: {P(a) == True{} : Bool}) -> {P(b) == True{} : Bool}:
  %e : {P(_) == True{} : Bool}
  fact

def lo6(cp: U32) -> Word(6n):
  W.adjust(6n, 32n, X.bits(cp))

def hi2(cp: U32) -> Word(5n):
  W.adjust(5n, 32n, X.bits(U32.shrn(cp, 6n)))

def hi3(cp: U32) -> Word(4n):
  W.adjust(4n, 32n, X.bits(U32.shrn(cp, 12n)))

def hi4(cp: U32) -> Word(3n):
  W.adjust(3n, 32n, X.bits(U32.shrn(cp, 18n)))

law code_form2:
  for +cp: U32
  for limit: {U32.is_lt(cp, 2048) == True{} : Bool}
  {cp == X.scalar2(hi2(cp), lo6(cp)) : U32}
def code_form2(cp, limit):
  match cp:
    case U32{+w}:
      match w:
        case WCon{+w0, WCon{+w1, WCon{+w2, WCon{+w3, WCon{+w4, WCon{+w5, WCon{+w6, WCon{+w7, WCon{+w8, WCon{+w9, WCon{+w10, +rest}}}}}}}}}}}:
          reads = Equal.trans(Bool, U32.is_le(cp, 2047), U32.is_lt(cp, 2048), True{}, U.limit_u32_successor(cp, 2047, {==}), limit)
          Equal.cong(Word(32n), U32, z => U32{z}, w, W.join(11n, 21n, W.adjust(11n, 32n, w), Word.zero(21n)), W.limit_bits_low(11n, 21n, w, reads))

law code_form3:
  for +cp: U32
  for limit: {U32.is_lt(cp, 65536) == True{} : Bool}
  {cp == X.scalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)) : U32}
def code_form3(cp, limit):
  match cp:
    case U32{+w}:
      match w:
        case WCon{+w0, WCon{+w1, WCon{+w2, WCon{+w3, WCon{+w4, WCon{+w5, WCon{+w6, WCon{+w7, WCon{+w8, WCon{+w9, WCon{+w10, WCon{+w11, WCon{+w12, WCon{+w13, WCon{+w14, WCon{+w15, +rest}}}}}}}}}}}}}}}}:
          reads = Equal.trans(Bool, U32.is_le(cp, 65535), U32.is_lt(cp, 65536), True{}, U.limit_u32_successor(cp, 65535, {==}), limit)
          Equal.cong(Word(32n), U32, z => U32{z}, w, W.join(16n, 16n, W.adjust(16n, 32n, w), Word.zero(16n)), W.limit_bits_low(16n, 16n, w, reads))

law code_form4:
  for +cp: U32
  for limit: {U32.is_lt(cp, 2097152) == True{} : Bool}
  {cp == X.scalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)) : U32}
def code_form4(cp, limit):
  match cp:
    case U32{+w}:
      match w:
        case WCon{+w0, WCon{+w1, WCon{+w2, WCon{+w3, WCon{+w4, WCon{+w5, WCon{+w6, WCon{+w7, WCon{+w8, WCon{+w9, WCon{+w10, WCon{+w11, WCon{+w12, WCon{+w13, WCon{+w14, WCon{+w15, WCon{+w16, WCon{+w17, WCon{+w18, WCon{+w19, WCon{+w20, +rest}}}}}}}}}}}}}}}}}}}}}:
          reads = Equal.trans(Bool, U32.is_le(cp, 2097151), U32.is_lt(cp, 2097152), True{}, U.limit_u32_successor(cp, 2097151, {==}), limit)
          Equal.cong(Word(32n), U32, z => U32{z}, w, W.join(21n, 11n, W.adjust(21n, 32n, w), Word.zero(11n)), W.limit_bits_low(21n, 11n, w, reads))

law traverse_emit_form2:
  for +hi: Word(5n)
  for +b0: Word(6n)
  for +acc: String
  for minimum: {U32.is_ge(X.scalar2(hi, b0), 128) == True{} : Bool}
  for valid: {B.code_valid(X.scalar2(hi, b0)) == True{} : Bool}
  {T.traverse_text(B.utf8_code_emit(X.scalar2(hi, b0), False{}, True{}, False{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar2(hi, b0)}, acc}} : T.TextValue}
def traverse_emit_form2(hi, b0, acc, minimum, valid):
  %Equal.sym(List<&2, U32>, B.utf8_code_emit(X.scalar2(hi, b0), False{}, True{}, False{}), [I.prefix2(hi), X.continuation(b0)], X.utf8_form_2_bytes(hi, b0)) :
    {T.traverse_text(_, T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar2(hi, b0)}, acc}} : T.TextValue}
  traverse_form2(hi, b0, acc, minimum, valid)

law traverse_emit_form3:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +acc: String
  for minimum: {U32.is_ge(X.scalar3(hi, b0, b1), 2048) == True{} : Bool}
  for valid: {B.code_valid(X.scalar3(hi, b0, b1)) == True{} : Bool}
  {T.traverse_text(B.utf8_code_emit(X.scalar3(hi, b0, b1), False{}, False{}, True{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar3(hi, b0, b1)}, acc}} : T.TextValue}
def traverse_emit_form3(hi, b0, b1, acc, minimum, valid):
  %Equal.sym(List<&2, U32>, B.utf8_code_emit(X.scalar3(hi, b0, b1), False{}, False{}, True{}), [I.prefix3(hi), X.continuation(b0), X.continuation(b1)], X.utf8_form_3_bytes(hi, b0, b1)) :
    {T.traverse_text(_, T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar3(hi, b0, b1)}, acc}} : T.TextValue}
  traverse_form3(hi, b0, b1, acc, minimum, valid)

law traverse_emit_form4:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for +acc: String
  for minimum: {U32.is_ge(X.scalar4(hi, b0, b1, b2), 65536) == True{} : Bool}
  for valid: {B.code_valid(X.scalar4(hi, b0, b1, b2)) == True{} : Bool}
  {T.traverse_text(B.utf8_code_emit(X.scalar4(hi, b0, b1, b2), False{}, False{}, False{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
def traverse_emit_form4(hi, b0, b1, b2, acc, minimum, valid):
  %Equal.sym(List<&2, U32>, B.utf8_code_emit(X.scalar4(hi, b0, b1, b2), False{}, False{}, False{}), [I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(b2)], X.utf8_form_4_bytes(hi, b0, b1, b2)) :
    {T.traverse_text(_, T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{X.scalar4(hi, b0, b1, b2)}, acc}} : T.TextValue}
  traverse_form4(hi, b0, b1, b2, acc, minimum, valid)

law traverse_code2:
  for +cp: U32
  for +acc: String
  for limit: {U32.is_lt(cp, 2048) == True{} : Bool}
  for minimum: {U32.is_ge(cp, 128) == True{} : Bool}
  for valid: {B.code_valid(cp) == True{} : Bool}
  {T.traverse_text(B.utf8_code_emit(cp, False{}, True{}, False{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{cp}, acc}} : T.TextValue}
def traverse_code2(cp, acc, limit, minimum, valid):
  +form = code_form2(cp, limit)
  m = fact_transferred(z => U32.is_ge(z, 128), cp, X.scalar2(hi2(cp), lo6(cp)), form, minimum)
  v = fact_transferred(z => B.code_valid(z), cp, X.scalar2(hi2(cp), lo6(cp)), form, valid)
  %Equal.sym(U32, cp, X.scalar2(hi2(cp), lo6(cp)), form) :
    {T.traverse_text(B.utf8_code_emit(_, False{}, True{}, False{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{_}, acc}} : T.TextValue}
  traverse_emit_form2(hi2(cp), lo6(cp), acc, m, v)

law traverse_code3:
  for +cp: U32
  for +acc: String
  for limit: {U32.is_lt(cp, 65536) == True{} : Bool}
  for minimum: {U32.is_ge(cp, 2048) == True{} : Bool}
  for valid: {B.code_valid(cp) == True{} : Bool}
  {T.traverse_text(B.utf8_code_emit(cp, False{}, False{}, True{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{cp}, acc}} : T.TextValue}
def traverse_code3(cp, acc, limit, minimum, valid):
  +form = code_form3(cp, limit)
  m = fact_transferred(z => U32.is_ge(z, 2048), cp, X.scalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)), form, minimum)
  v = fact_transferred(z => B.code_valid(z), cp, X.scalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)), form, valid)
  %Equal.sym(U32, cp, X.scalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)), form) :
    {T.traverse_text(B.utf8_code_emit(_, False{}, False{}, True{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{_}, acc}} : T.TextValue}
  traverse_emit_form3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp), acc, m, v)

law traverse_code4:
  for +cp: U32
  for +acc: String
  for limit: {U32.is_lt(cp, 2097152) == True{} : Bool}
  for minimum: {U32.is_ge(cp, 65536) == True{} : Bool}
  for valid: {B.code_valid(cp) == True{} : Bool}
  {T.traverse_text(B.utf8_code_emit(cp, False{}, False{}, False{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{cp}, acc}} : T.TextValue}
def traverse_code4(cp, acc, limit, minimum, valid):
  +form = code_form4(cp, limit)
  m = fact_transferred(z => U32.is_ge(z, 65536), cp, X.scalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)), form, minimum)
  v = fact_transferred(z => B.code_valid(z), cp, X.scalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)), form, valid)
  %Equal.sym(U32, cp, X.scalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)), form) :
    {T.traverse_text(B.utf8_code_emit(_, False{}, False{}, False{}), T.Reading{C.Start{}, acc}) == T.Reading{C.Start{}, SCon{Chr{_}, acc}} : T.TextValue}
  traverse_emit_form4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp), acc, m, v)

law code_valid_fits_21_bits:
  for +cp: U32
  for valid: {B.code_valid(cp) == True{} : Bool}
  {U32.is_lt(cp, 2097152) == True{} : Bool}
def code_valid_fits_21_bits(cp, valid):
  reads = F.and_boolean_left(U32.is_le(cp, 1114111), U32.is_lt(cp, 55296) || U32.is_gt(cp, 57343), valid)
  lt = Equal.trans(Bool, U32.is_lt(cp, 1114112), U32.is_le(cp, 1114111), True{},
    Equal.sym(Bool, U32.is_le(cp, 1114111), U32.is_lt(cp, 1114112), U.limit_u32_successor(cp, 1114111, {==})), reads)
  U.u32_lt_transitive(cp, 1114112, 2097152, lt, {==})

law traverse_code_cases:
  for +cp: U32
  for ascii: Bool
  for two: Bool
  for three: Bool
  for +acc: String
  for a: {U32.is_lt(cp, 128) == ascii : Bool}
  for d: {U32.is_lt(cp, 2048) == two : Bool}
  for t: {U32.is_lt(cp, 65536) == three : Bool}
  for +valid: {B.code_valid(cp) == True{} : Bool}
  {T.traverse_text(B.utf8_code_emit(cp, ascii, two, three), T.Reading{C.Start{}, acc}) ==
    T.Reading{C.Start{}, SCon{Chr{cp}, acc}} : T.TextValue}
def traverse_code_cases(cp, ascii, two, three, acc, a, d, t, valid):
  match ascii two three:
    case True{} _ _:
      traverse_ascii(cp, acc, a)
    case False{} True{} _:
      traverse_code2(cp, acc, d, I.lt_false_and_ge(U32.cmp(cp, 128), a), valid)
    case False{} False{} True{}:
      traverse_code3(cp, acc, t, I.lt_false_and_ge(U32.cmp(cp, 2048), d), valid)
    case False{} False{} False{}:
      traverse_code4(cp, acc, code_valid_fits_21_bits(cp, valid), I.lt_false_and_ge(U32.cmp(cp, 65536), t), valid)

# Universal scalar completeness, using the ORIGINAL contract range selection.
law utf8_code_emits_exactly_o_scalar:
  for +cp: U32
  for +acc: String
  for valid: {B.code_valid(cp) == True{} : Bool}
  {T.traverse_text(B.utf8_code(cp), T.Reading{C.Start{}, acc}) ==
    T.Reading{C.Start{}, SCon{Chr{cp}, acc}} : T.TextValue}
def utf8_code_emits_exactly_o_scalar(cp, acc, valid):
  traverse_code_cases(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536), acc, {==}, {==}, {==}, valid)

law traverse_concatenation:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +t: T.TextValue
  {T.traverse_text(B.concatenate(a, b), t) == T.traverse_text(b, T.traverse_text(a, t)) : T.TextValue}
def traverse_concatenation(a, b, t):
  match a:
    case Nil{}:
      {==}
    case Con{h, rest}:
      traverse_concatenation(rest, b, T.step_text(t, h))

# Induction on text, preserving an arbitrary parser accumulator.
law utf8_text_emits_exactly_o_text_inverted:
  for +s: String
  for +acc: String
  for +valid: {B.text_valid(s) == True{} : Bool}
  {T.traverse_text(B.utf8(s), T.Reading{C.Start{}, acc}) ==
    T.Reading{C.Start{}, String.reverse.go(s, acc)} : T.TextValue}
def utf8_text_emits_exactly_o_text_inverted(s, acc, valid):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +tail}:
      %Equal.sym(T.TextValue,
        T.traverse_text(B.concatenate(B.utf8_code(cp), B.utf8(tail)), T.Reading{C.Start{}, acc}),
        T.traverse_text(B.utf8(tail), T.traverse_text(B.utf8_code(cp), T.Reading{C.Start{}, acc})),
        traverse_concatenation(B.utf8_code(cp), B.utf8(tail), T.Reading{C.Start{}, acc})) :
        {_ == T.Reading{C.Start{}, String.reverse.go(tail, SCon{Chr{cp}, acc})} : T.TextValue}
      %Equal.sym(T.TextValue,
        T.traverse_text(B.utf8_code(cp), T.Reading{C.Start{}, acc}), T.Reading{C.Start{}, SCon{Chr{cp}, acc}},
        utf8_code_emits_exactly_o_scalar(cp, acc, F.and_boolean_left(B.code_valid(cp), B.text_valid(tail), valid))) :
        {T.traverse_text(B.utf8(tail), _) == T.Reading{C.Start{}, String.reverse.go(tail, SCon{Chr{cp}, acc})} : T.TextValue}
      utf8_text_emits_exactly_o_text_inverted(tail, SCon{Chr{cp}, acc}, F.and_boolean_right(B.code_valid(cp), B.text_valid(tail), valid))

law reverse_accumulator_double:
  for +s: String
  for +a: String
  for +b: String
  {String.reverse.go(String.reverse.go(s, a), b) == String.reverse.go(a, String.append(s, b)) : String}
def reverse_accumulator_double(s, a, b):
  match s:
    case SNil{}:
      {==}
    case SCon{h, tail}:
      reverse_accumulator_double(tail, SCon{h, a}, b)

law append_empty_right:
  for +s: String
  {String.append(s, "") == s : String}
def append_empty_right(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, tail}:
      Equal.cong(String, String, r => SCon{h, r}, String.append(tail, ""), tail, append_empty_right(tail))

law reverse_double:
  for +s: String
  {String.reverse(String.reverse(s)) == s : String}
def reverse_double(s):
  Equal.trans(String, String.reverse(String.reverse(s)), String.append(s, ""), s,
    reverse_accumulator_double(s, "", ""), append_empty_right(s))

# Complete roundtrip of every valid String; no size bound.
law utf8_text_valid_decodes_exactly:
  for +s: String
  for valid: {B.text_valid(s) == True{} : Bool}
  {T.finalize_text(T.traverse_text(B.utf8(s), T.Reading{C.Start{}, ""})) == Some{s} : Maybe<&2, String>}
def utf8_text_valid_decodes_exactly(s, valid):
  %Equal.sym(T.TextValue, T.traverse_text(B.utf8(s), T.Reading{C.Start{}, ""}), T.Reading{C.Start{}, String.reverse(s)}, utf8_text_emits_exactly_o_text_inverted(s, "", valid)) :
    {T.finalize_text(_) == Some{s} : Maybe<&2, String>}
  Equal.cong(String, Maybe<&2, String>, r => Some{r}, String.reverse(String.reverse(s)), s, reverse_double(s))
