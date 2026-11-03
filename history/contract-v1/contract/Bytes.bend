import Base

# Byte sequences are U32 lists accompanied by octets_all_valid.
# No conversion below normalizes Unicode, replaces characters or truncates
# messages. The TextEncoded relation explicitly requires valid text.

def length(bs: List<&2, U32>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+length(t)

def concatenate(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      b
    case Con{h, t}:
      Con{h, concatenate(t, b)}

def octets_all_valid(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{h, t}:
      U32.is_le(h, 255) && octets_all_valid(t)

def code_valid(+cp: U32) -> Bool:
  U32.is_le(cp, 1114111) && (U32.is_lt(cp, 55296) || U32.is_gt(cp, 57343))

def text_valid(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{cp}, tail}:
      code_valid(cp) && text_valid(tail)

def be32(+x: U32) -> List<&2, U32>:
  [U32.and(U32.shrn(x, 24n), 255),
   U32.and(U32.shrn(x, 16n), 255),
   U32.and(U32.shrn(x, 8n), 255),
   U32.and(x, 255)]

def be64(high: U32, low: U32) -> List<&2, U32>:
  concatenate(be32(high), be32(low))

def utf8_code_emit(+cp: U32, ascii: Bool, two: Bool, three: Bool) -> List<&2, U32>:
  match ascii two three:
    case True{} _ _:
      [cp]
    case False{} True{} _:
      [U32.or(192, U32.shrn(cp, 6n)),
       U32.or(128, U32.and(cp, 63))]
    case False{} False{} True{}:
      [U32.or(224, U32.shrn(cp, 12n)),
       U32.or(128, U32.and(U32.shrn(cp, 6n), 63)),
       U32.or(128, U32.and(cp, 63))]
    case False{} False{} False{}:
      [U32.or(240, U32.shrn(cp, 18n)),
       U32.or(128, U32.and(U32.shrn(cp, 12n), 63)),
       U32.or(128, U32.and(U32.shrn(cp, 6n), 63)),
       U32.or(128, U32.and(cp, 63))]

def utf8_code(+cp: U32) -> List<&2, U32>:
  utf8_code_emit(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536))

def utf8(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{cp}, tail}:
      concatenate(utf8_code(cp), utf8(tail))

# UTF-8 recognizer state. Minimum values prohibit encodings
# longer than necessary. code_valid excludes surrogates and values
# above U+10FFFF. Invalid leading or trailing bytes produce Invalid.
type Decoder is Data:
  Invalid{}
  Dec{missing: Nat, accumulated: U32, minimum: U32}

def select_dec(valid: Bool, state: Decoder) -> Decoder:
  match valid:
    case False{}:
      Invalid{}
    case True{}:
      state

def start_code(+b: U32, ascii: Bool, two: Bool, three: Bool, four: Bool) -> Decoder:
  match ascii two three four:
    case True{} _ _ _:
      Dec{0n, 0, 0}
    case False{} True{} _ _:
      Dec{1n, (b - 192 : U32), 128}
    case False{} False{} True{} _:
      Dec{2n, (b - 224 : U32), 2048}
    case False{} False{} False{} True{}:
      Dec{3n, (b - 240 : U32), 65536}
    case False{} False{} False{} False{}:
      Invalid{}

def start(+b: U32) -> Decoder:
  start_code(b, U32.is_lt(b, 128),
    U32.is_ge(b, 194) && U32.is_le(b, 223),
    U32.is_ge(b, 224) && U32.is_le(b, 239),
    U32.is_ge(b, 240) && U32.is_le(b, 244))

def resume_end(missing: Nat, +cp: U32, minimum: U32) -> Decoder:
  match missing:
    case 0n:
      select_dec(U32.is_ge(cp, minimum) && code_valid(cp), Dec{0n, 0, 0})
    case 1n+p:
      Dec{1n+p, cp, minimum}

def resume(missing: Nat, accumulated: U32, minimum: U32, +b: U32) -> Decoder:
  select_dec(U32.is_ge(b, 128) && U32.is_le(b, 191),
    resume_end(missing, (accumulated * 64 + b - 128 : U32), minimum))

def step(state: Decoder, b: U32) -> Decoder:
  match state:
    case Invalid{}:
      Invalid{}
    case Dec{0n, accumulated, minimum}:
      start(b)
    case Dec{1n+p, accumulated, minimum}:
      resume(p, accumulated, minimum, b)

def end(state: Decoder) -> Bool:
  match state:
    case Invalid{}:
      False{}
    case Dec{0n, accumulated, minimum}:
      True{}
    case Dec{1n+p, accumulated, minimum}:
      False{}

def utf8_recognize(bs: List<&2, U32>, state: Decoder) -> Bool:
  match bs:
    case Nil{}:
      end(state)
    case Con{h, t}:
      utf8_recognize(t, step(state, h))

def utf8_valid(bs: List<&2, U32>) -> Bool:
  utf8_recognize(bs, Dec{0n, 0, 0})

def TextEncoded(+text: String, bytes: List<&2, U32>) -> Type:
  {text_valid(text) == True{} : Bool} &
  {utf8(text) == bytes : List<&2, U32>}

def Octets(bytes: List<&2, U32>) -> Type:
  {octets_all_valid(bytes) == True{} : Bool}

def Word64(high: U32, low: U32, bytes: List<&2, U32>) -> Type:
  {be64(high, low) == bytes : List<&2, U32>}

# Length conversion without truncation. Addition checks the carry
# before using U32 arithmetic. Above the largest u64, the result is None.
type Number64 is Data:
  Number64{high: U32, low: U32}

def increment64_cases(+high: U32, low: U32, transport: Bool, exhausted: Bool) -> Maybe<&2, Number64>:
  match transport exhausted:
    case False{} _:
      Some{Number64{high, (low + 1 : U32)}}
    case True{} False{}:
      Some{Number64{(high + 1 : U32), 0}}
    case True{} True{}:
      None{}

def increment64(x: Maybe<&2, Number64>) -> Maybe<&2, Number64>:
  match x:
    case None{}:
      None{}
    case Some{Number64{+high, +low}}:
      increment64_cases(high, low, U32.is_eq(low, 4294967295), U32.is_eq(high, 4294967295))

def nat64(n: Nat) -> Maybe<&2, Number64>:
  match n:
    case 0n:
      Some{Number64{0, 0}}
    case 1n+p:
      increment64(nat64(p))

def number64_bytes(x: Maybe<&2, Number64>) -> Maybe<&2, List<&2, U32>>:
  match x:
    case None{}:
      None{}
    case Some{Number64{high, low}}:
      Some{be64(high, low)}

def length64(n: Nat) -> Maybe<&2, List<&2, U32>>:
  number64_bytes(nat64(n))

def fits64(x: Maybe<&2, Number64>) -> Bool:
  match x:
    case None{}:
      False{}
    case Some{number}:
      True{}

def length_representable(n: Nat) -> Bool:
  fits64(nat64(n))
