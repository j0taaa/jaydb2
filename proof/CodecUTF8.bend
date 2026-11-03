# General simulation between the parser UTF-8 transducer and the original
# contract/Bytes recognizer. No character/byte enumeration.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C

# The transducer never stores Continue{0,...}: the last byte produces Character.
def UnicodeNormal(u: C.Unicode) -> Type:
  match u:
    case C.Start{}:
      Unit
    case C.Continue{0n, cp, minimum}:
      Empty
    case C.Continue{1n+p, cp, minimum}:
      Unit

def ScalarNormal(e: C.Scalar) -> Type:
  match e:
    case C.Partial{u}:
      UnicodeNormal(u)
    case _:
      Unit

def represent(u: C.Unicode) -> B.Decoder:
  match u:
    case C.Start{}:
      B.Dec{0n, 0, 0}
    case C.Continue{n, cp, minimum}:
      B.Dec{n, cp, minimum}

def mirror(e: C.Scalar) -> B.Decoder:
  match e:
    case C.UTFInvalid{}:
      B.Invalid{}
    case C.Character{cp}:
      B.Dec{0n, 0, 0}
    case C.Partial{u}:
      represent(u)

law scalar_checked_mirrors_recognizer:
  for ok: Bool
  for cp: U32
  {mirror(C.scalar_checked(ok, cp)) == B.select_dec(ok, B.Dec{0n, 0, 0}) : B.Decoder}
def scalar_checked_mirrors_recognizer(ok, cp):
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

law complete_utf8_mirrors_recognizer:
  for n: Nat
  for +cp: U32
  for +minimum: U32
  {mirror(C.complete_utf8(n, cp, minimum)) == B.resume_end(n, cp, minimum) : B.Decoder}
def complete_utf8_mirrors_recognizer(n, cp, minimum):
  match n:
    case 0n:
      scalar_checked_mirrors_recognizer(U32.is_ge(cp, minimum) && B.code_valid(cp), cp)
    case 1n+p:
      {==}

law resume_utf8_mirrors_recognizer:
  for ok: Bool
  for +n: Nat
  for +cp: U32
  for +minimum: U32
  for +b: U32
  {mirror(C.resume_utf8(ok, n, cp, minimum, b)) ==
    B.select_dec(ok, B.resume_end(n, (cp * 64 + b - 128 : U32), minimum)) : B.Decoder}
def resume_utf8_mirrors_recognizer(ok, n, cp, minimum, b):
  match ok:
    case False{}:
      {==}
    case True{}:
      complete_utf8_mirrors_recognizer(n, (cp * 64 + b - 128 : U32), minimum)

law start_utf8_mirrors_recognizer:
  for ascii: Bool
  for two: Bool
  for three: Bool
  for four: Bool
  for +b: U32
  {mirror(C.start_utf8(ascii, two, three, four, b)) == B.start_code(b, ascii, two, three, four) : B.Decoder}
def start_utf8_mirrors_recognizer(ascii, two, three, four, b):
  match ascii two three four:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} True{} _:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

law step_utf8_mirrors_recognizer_original:
  for +u: C.Unicode
  for +b: U32
  for normal: UnicodeNormal(u)
  {mirror(C.step_utf8(u, b)) == B.step(represent(u), b) : B.Decoder}
def step_utf8_mirrors_recognizer_original(u, b, normal):
  match u:
    case C.Start{}:
      start_utf8_mirrors_recognizer(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case C.Continue{0n, cp, minimum}:
      L.ex_false({mirror(C.step_utf8(C.Continue{0n, cp, minimum}, b)) == B.step(represent(C.Continue{0n, cp, minimum}), b) : B.Decoder}, normal)
    case C.Continue{1n+p, +cp, +minimum}:
      resume_utf8_mirrors_recognizer(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimum, b)

def scalar_checked_normal(ok: Bool, cp: U32) -> ScalarNormal(C.scalar_checked(ok, cp)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Unit{}


law complete_utf8_produces_state_normal:
  for n: Nat
  for +cp: U32
  for +minimum: U32
  ScalarNormal(C.complete_utf8(n, cp, minimum))
def complete_utf8_produces_state_normal(n, cp, minimum):
  match n:
    case 0n:
      scalar_checked_normal(U32.is_ge(cp, minimum) && B.code_valid(cp), cp)
    case 1n+p:
      Unit{}

law resume_utf8_produces_state_normal:
  for ok: Bool
  for +n: Nat
  for +cp: U32
  for +minimum: U32
  for +b: U32
  ScalarNormal(C.resume_utf8(ok, n, cp, minimum, b))
def resume_utf8_produces_state_normal(ok, n, cp, minimum, b):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      complete_utf8_produces_state_normal(n, (cp * 64 + b - 128 : U32), minimum)

law start_utf8_produces_state_normal:
  for ascii: Bool
  for two: Bool
  for three: Bool
  for four: Bool
  for b: U32
  ScalarNormal(C.start_utf8(ascii, two, three, four, b))
def start_utf8_produces_state_normal(ascii, two, three, four, b):
  match ascii two three four:
    case True{} _ _ _:
      Unit{}
    case False{} True{} _ _:
      Unit{}
    case False{} False{} True{} _:
      Unit{}
    case False{} False{} False{} True{}:
      Unit{}
    case False{} False{} False{} False{}:
      Unit{}

law step_utf8_produces_state_normal:
  for u: C.Unicode
  for +b: U32
  ScalarNormal(C.step_utf8(u, b))
def step_utf8_produces_state_normal(u, b):
  match u:
    case C.Start{}:
      start_utf8_produces_state_normal(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case C.Continue{0n, cp, minimum}:
      Unit{}
    case C.Continue{1n+p, cp, minimum}:
      resume_utf8_produces_state_normal(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimum, b)

# Executes the same transduction, keeping the text but no outer counter.
# This helper machine separates UTF-8 inversion from the u64 proof.
type TextValue is Data:
  TextInvalid{}
  Reading{unicode: C.Unicode, inverted: String}

def join(e: C.Scalar, inverted: String) -> TextValue:
  match e:
    case C.UTFInvalid{}:
      TextInvalid{}
    case C.Character{cp}:
      Reading{C.Start{}, SCon{Chr{cp}, inverted}}
    case C.Partial{u}:
      Reading{u, inverted}

def step_text(t: TextValue, b: U32) -> TextValue:
  match t:
    case TextInvalid{}:
      TextInvalid{}
    case Reading{u, inverted}:
      join(C.step_utf8(u, b), inverted)

def TextNormal(t: TextValue) -> Type:
  match t:
    case TextInvalid{}:
      Unit
    case Reading{u, inverted}:
      UnicodeNormal(u)

def represent_text(t: TextValue) -> B.Decoder:
  match t:
    case TextInvalid{}:
      B.Invalid{}
    case Reading{u, inverted}:
      represent(u)

def finalize_text(t: TextValue) -> Maybe<&2, String>:
  match t:
    case TextInvalid{}:
      None{}
    case Reading{C.Start{}, inverted}:
      Some{String.reverse(inverted)}
    case Reading{C.Continue{n, cp, minimum}, inverted}:
      None{}

def traverse_text(bs: List<&2, U32>, t: TextValue) -> TextValue:
  match bs:
    case Nil{}:
      t
    case Con{b, rest}:
      traverse_text(rest, step_text(t, b))

law join_mirrors_scalar:
  for e: C.Scalar
  for inverted: String
  {represent_text(join(e, inverted)) == mirror(e) : B.Decoder}
def join_mirrors_scalar(e, inverted):
  match e:
    case C.UTFInvalid{}:
      {==}
    case C.Character{cp}:
      {==}
    case C.Partial{u}:
      {==}

law join_preserves_normal:
  for +e: C.Scalar
  for inverted: String
  for normal: ScalarNormal(e)
  TextNormal(join(e, inverted))
def join_preserves_normal(e, inverted, normal):
  match e:
    case C.UTFInvalid{}:
      Unit{}
    case C.Character{cp}:
      Unit{}
    case C.Partial{u}:
      normal

law step_text_preserves_normal:
  for +t: TextValue
  for +b: U32
  TextNormal(step_text(t, b))
def step_text_preserves_normal(t, b):
  match t:
    case TextInvalid{}:
      Unit{}
    case Reading{+u, inverted}:
      join_preserves_normal(C.step_utf8(u, b), inverted, step_utf8_produces_state_normal(u, b))

law step_text_mirrors_recognizer:
  for +t: TextValue
  for +b: U32
  for normal: TextNormal(t)
  {represent_text(step_text(t, b)) == B.step(represent_text(t), b) : B.Decoder}
def step_text_mirrors_recognizer(t, b, normal):
  match t:
    case TextInvalid{}:
      {==}
    case Reading{+u, inverted}:
      Equal.trans(B.Decoder, represent_text(join(C.step_utf8(u, b), inverted)), mirror(C.step_utf8(u, b)), B.step(represent(u), b),
        join_mirrors_scalar(C.step_utf8(u, b), inverted), step_utf8_mirrors_recognizer_original(u, b, normal))

def has_text(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      True{}

law finalize_text_mirrors_recognizer:
  for +t: TextValue
  for normal: TextNormal(t)
  {has_text(finalize_text(t)) == B.end(represent_text(t)) : Bool}
def finalize_text_mirrors_recognizer(t, normal):
  match t:
    case TextInvalid{}:
      {==}
    case Reading{C.Start{}, inverted}:
      {==}
    case Reading{C.Continue{0n, cp, minimum}, inverted}:
      L.ex_false({False{} == True{} : Bool}, normal)
    case Reading{C.Continue{1n+p, cp, minimum}, inverted}:
      {==}

law transduction_utf8_accepts_exactly_o_recognizer:
  for +bs: List<&2, U32>
  for +t: TextValue
  for normal: TextNormal(t)
  {has_text(finalize_text(traverse_text(bs, t))) == B.utf8_recognize(bs, represent_text(t)) : Bool}
def transduction_utf8_accepts_exactly_o_recognizer(bs, t, normal):
  match bs:
    case Nil{}:
      finalize_text_mirrors_recognizer(t, normal)
    case Con{+b, +rest}:
      %step_text_mirrors_recognizer(t, b, normal) :
        {has_text(finalize_text(traverse_text(rest, step_text(t, b)))) == B.utf8_recognize(rest, _) : Bool}
      transduction_utf8_accepts_exactly_o_recognizer(rest, step_text(t, b), step_text_preserves_normal(t, b))

law utf8_of_parser_and_of_contract_accept_os_same_bytes:
  for +bs: List<&2, U32>
  {has_text(finalize_text(traverse_text(bs, Reading{C.Start{}, ""}))) == B.utf8_valid(bs) : Bool}
def utf8_of_parser_and_of_contract_accept_os_same_bytes(bs):
  transduction_utf8_accepts_exactly_o_recognizer(bs, Reading{C.Start{}, ""}, Unit{})
