# Independent mathematical decimal parser, preserving an explicit token boundary.
import Base
import ./DecimalDivision.bend as D
import ../contract/Bytes.bend as B
import ./Foundations.bend as F
import ./CodecWordsWord.bend as W
import ./CodecRelaxArithmeticWord.bend as Measures
import ./CodecSums64.bend as C64

def append(xs: List<&2, D.Digit>, ys: List<&2, D.Digit>) -> List<&2, D.Digit>:
  match xs:
    case Nil{}: ys
    case Con{d, rest}: Con{d, append(rest, ys)}

def render(xs: List<&2, D.Digit>) -> String:
  match xs:
    case Nil{}: ""
    case Con{d, rest}: SCon{D.digit_char(d), render(rest)}

def evaluate(xs: List<&2, D.Digit>, accumulator: Nat) -> Nat:
  match xs:
    case Nil{}: accumulator
    case Con{d, rest}: evaluate(rest, Nat.add(Nat.mul(accumulator, 10n), D.digit_nat(d)))

def value(xs: List<&2, D.Digit>) -> Nat:
  evaluate(xs, 0n)

law rendered_append:
  for +xs: List<&2, D.Digit>
  for +ys: List<&2, D.Digit>
  {render(append(xs, ys)) == render(xs) ++ render(ys) : String}
def rendered_append(xs, ys):
  match xs:
    case Nil{}: {==}
    case Con{+d, +rest}:
      Equal.cong(String, String, s => SCon{D.digit_char(d), s},
        render(append(rest, ys)), render(rest) ++ render(ys), rendered_append(rest, ys))

law evaluated_append:
  for +xs: List<&2, D.Digit>
  for +ys: List<&2, D.Digit>
  for +accumulator: Nat
  {evaluate(append(xs, ys), accumulator) == evaluate(ys, evaluate(xs, accumulator)) : Nat}
def evaluated_append(xs, ys, accumulator):
  match xs:
    case Nil{}: {==}
    case Con{d, rest}: evaluated_append(rest, ys, Nat.add(Nat.mul(accumulator, 10n), D.digit_nat(d)))

law appended_digit_value:
  for +xs: List<&2, D.Digit>
  for +d: D.Digit
  {value(append(xs, [d])) == Nat.add(Nat.mul(value(xs), 10n), D.digit_nat(d)) : Nat}
def appended_digit_value(xs, d):
  evaluated_append(xs, [d], 0n)

def read_digit(c: Char) -> Maybe<&2, D.Digit>:
  match c:
    case '0': Some{D.D0{}}
    case '1': Some{D.D1{}}
    case '2': Some{D.D2{}}
    case '3': Some{D.D3{}}
    case '4': Some{D.D4{}}
    case '5': Some{D.D5{}}
    case '6': Some{D.D6{}}
    case '7': Some{D.D7{}}
    case '8': Some{D.D8{}}
    case '9': Some{D.D9{}}
    case _: None{}

law digit_roundtrip:
  for +d: D.Digit
  {read_digit(D.digit_char(d)) == Some{d} : Maybe<&2, D.Digit>}
def digit_roundtrip(d):
  match d:
    case D.D0{}: {==}
    case D.D1{}: {==}
    case D.D2{}: {==}
    case D.D3{}: {==}
    case D.D4{}: {==}
    case D.D5{}: {==}
    case D.D6{}: {==}
    case D.D7{}: {==}
    case D.D8{}: {==}
    case D.D9{}: {==}

type Parsed is Data:
  Invalid{}
  Parsed{number: Nat, rest: String}

def scan_digit(digit: Maybe<&2, D.Digit>, raw: String, accumulator: Nat, next: Nat -> Parsed) -> Parsed:
  match digit:
    case None{}: Parsed{accumulator, raw}
    case Some{d}: next(Nat.add(Nat.mul(accumulator, 10n), D.digit_nat(d)))

def scan(raw: String, accumulator: Nat) -> Parsed:
  match raw:
    case SNil{}: Parsed{accumulator, ""}
    case SCon{+h, +tail}: scan_digit(read_digit(h), SCon{h, tail}, accumulator, next => scan(tail, next))

def initial(digit: Maybe<&2, D.Digit>, tail: String) -> Parsed:
  match digit:
    case None{}: Invalid{}
    case Some{d}: scan(tail, D.digit_nat(d))

def parse(raw: String) -> Parsed:
  match raw:
    case SNil{}: Invalid{}
    case SCon{h, tail}: initial(read_digit(h), tail)

# A real source-token delimiter is retained, rather than merged into a number.
# These constructors cover the Generate.instance_content comma and closing ')'.
type Boundary<-raw: String> is Type:
  EndBoundary{same: {raw == "" : String}}
  CommaBoundary{tail: String, same: {raw == SCon{',', tail} : String}}
  ParenBoundary{tail: String, same: {raw == SCon{')', tail} : String}}
  SpaceBoundary{tail: String, same: {raw == SCon{' ', tail} : String}}
  NewlineBoundary{tail: String, same: {raw == SCon{'\n', tail} : String}}

law scan_stops_at_boundary:
  for +raw: String
  for +accumulator: Nat
  for boundary: Boundary<raw>
  {scan(raw, accumulator) == Parsed{accumulator, raw} : Parsed}
def scan_stops_at_boundary(raw, accumulator, boundary):
  match boundary:
    case EndBoundary{same}:
      %Equal.sym(String, raw, "", same) : {scan(_, accumulator) == Parsed{accumulator, _} : Parsed}
      {==}
    case CommaBoundary{+tail, same}:
      %Equal.sym(String, raw, SCon{',', tail}, same) : {scan(_, accumulator) == Parsed{accumulator, _} : Parsed}
      {==}
    case ParenBoundary{+tail, same}:
      %Equal.sym(String, raw, SCon{')', tail}, same) : {scan(_, accumulator) == Parsed{accumulator, _} : Parsed}
      {==}
    case SpaceBoundary{+tail, same}:
      %Equal.sym(String, raw, SCon{' ', tail}, same) : {scan(_, accumulator) == Parsed{accumulator, _} : Parsed}
      {==}
    case NewlineBoundary{+tail, same}:
      %Equal.sym(String, raw, SCon{'\n', tail}, same) : {scan(_, accumulator) == Parsed{accumulator, _} : Parsed}
      {==}

law scan_rendered_digits:
  for +xs: List<&2, D.Digit>
  for +accumulator: Nat
  for +rest: String
  for boundary: Boundary<rest>
  {scan(render(xs) ++ rest, accumulator) == Parsed{evaluate(xs, accumulator), rest} : Parsed}
def scan_rendered_digits(xs, accumulator, rest, boundary):
  match xs:
    case Nil{}: scan_stops_at_boundary(rest, accumulator, boundary)
    case Con{+d, +tail}:
      %Equal.sym(Maybe<&2, D.Digit>, read_digit(D.digit_char(d)), Some{d}, digit_roundtrip(d)) :
        {scan_digit(_, SCon{D.digit_char(d), render(tail) ++ rest}, accumulator, next => scan(render(tail) ++ rest, next)) ==
          Parsed{evaluate(tail, Nat.add(Nat.mul(accumulator, 10n), D.digit_nat(d))), rest} : Parsed}
      scan_rendered_digits(tail, Nat.add(Nat.mul(accumulator, 10n), D.digit_nat(d)), rest, boundary)

law parse_nonempty_rendered_digits:
  for +head: D.Digit
  for +tail: List<&2, D.Digit>
  for +rest: String
  for boundary: Boundary<rest>
  {parse(render(Con{head, tail}) ++ rest) == Parsed{value(Con{head, tail}), rest} : Parsed}
def parse_nonempty_rendered_digits(head, tail, rest, boundary):
  %Equal.sym(Maybe<&2, D.Digit>, read_digit(D.digit_char(head)), Some{head}, digit_roundtrip(head)) :
    {initial(_, render(tail) ++ rest) == Parsed{value(Con{head, tail}), rest} : Parsed}
  scan_rendered_digits(tail, D.digit_nat(head), rest, boundary)

# Recovery is checked: numbers outside U32 cannot silently wrap.
type WordParsed is Data:
  WordInvalid{}
  WordParsed{word: U32, rest: String}

def low_word(zero: Bool, low: U32, rest: String) -> WordParsed:
  match zero:
    case False{}: WordInvalid{}
    case True{}: WordParsed{low, rest}

def checked_word(number: Maybe<&2, B.Number64>, rest: String) -> WordParsed:
  match number:
    case None{}: WordInvalid{}
    case Some{B.Number64{high, low}}: low_word(U32.is_zero(high), low, rest)

def word_result(parsed: Parsed) -> WordParsed:
  match parsed:
    case Invalid{}: WordInvalid{}
    case Parsed{number, rest}: checked_word(B.nat64(number), rest)

def parse_word(raw: String) -> WordParsed:
  word_result(parse(raw))

law zero_word_measure:
  for +n: Nat
  {Word.to_nat(n, Word.zero(n)) == 0n : Nat}
def zero_word_measure(n):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, Word.to_nat(p, Word.zero(p)), 0n, zero_word_measure(p))

law zero_extension_measure:
  for +n: Nat
  for +m: Nat
  for +w: Word(n)
  {Word.to_nat(Nat.add(n, m), W.join(n, m, w, Word.zero(m))) == Word.to_nat(n, w) : Nat}
def zero_extension_measure(n, m, w):
  match n:
    case 0n: zero_word_measure(m)
    case 1n+p:
      match w:
        case WCon{False{}, +tail}:
          Equal.cong(Nat, Nat, Nat.double,
            Word.to_nat(Nat.add(p, m), W.join(p, m, tail, Word.zero(m))), Word.to_nat(p, tail), zero_extension_measure(p, m, tail))
        case WCon{True{}, +tail}:
          Equal.cong(Nat, Nat, n => 1n+Nat.double(n),
            Word.to_nat(Nat.add(p, m), W.join(p, m, tail, Word.zero(m))), Word.to_nat(p, tail), zero_extension_measure(p, m, tail))

law measured_u32_is_zero_extended:
  for +n: U32
  {B.nat64(U32.to_nat(n)) == Some{B.Number64{0, n}} : Maybe<&2, B.Number64>}
def measured_u32_is_zero_extended(n):
  match n:
    case U32{+w}:
      Equal.trans(Maybe<&2, B.Number64>, B.nat64(Word.to_nat(32n, w)),
        B.nat64(Word.to_nat(64n, W.join(32n, 32n, w, Word.zero(32n)))), Some{B.Number64{0, U32{w}}},
        Equal.cong(Nat, Maybe<&2, B.Number64>, B.nat64, Word.to_nat(32n, w),
          Word.to_nat(64n, W.join(32n, 32n, w, Word.zero(32n))),
          Equal.sym(Nat, Word.to_nat(64n, W.join(32n, 32n, w, Word.zero(32n))), Word.to_nat(32n, w), zero_extension_measure(32n, 32n, w))),
        Measures.nat64_measures_number(B.Number64{0, U32{w}}))

law parsed_exact_measure_recovers_word:
  for +n: U32
  for +rest: String
  {word_result(Parsed{U32.to_nat(n), rest}) == WordParsed{n, rest} : WordParsed}
def parsed_exact_measure_recovers_word(n, rest):
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(U32.to_nat(n)), Some{B.Number64{0, n}}, measured_u32_is_zero_extended(n)) :
    {checked_word(_, rest) == WordParsed{n, rest} : WordParsed}
  {==}
