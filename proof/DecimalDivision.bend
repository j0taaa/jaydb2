# Actual pinned Base binary long division by ten, with a mathematical invariant.
import Base
import ./Foundations.bend as F

type Digit is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

def digit_word(d: Digit) -> U32:
  match d:
    case D0{}: 0
    case D1{}: 1
    case D2{}: 2
    case D3{}: 3
    case D4{}: 4
    case D5{}: 5
    case D6{}: 6
    case D7{}: 7
    case D8{}: 8
    case D9{}: 9

def digit_nat(d: Digit) -> Nat:
  match d:
    case D0{}: 0n
    case D1{}: 1n
    case D2{}: 2n
    case D3{}: 3n
    case D4{}: 4n
    case D5{}: 5n
    case D6{}: 6n
    case D7{}: 7n
    case D8{}: 8n
    case D9{}: 9n

def digit_char(d: Digit) -> Char:
  match d:
    case D0{}: '0'
    case D1{}: '1'
    case D2{}: '2'
    case D3{}: '3'
    case D4{}: '4'
    case D5{}: '5'
    case D6{}: '6'
    case D7{}: '7'
    case D8{}: '8'
    case D9{}: '9'

def quotient_bit(d: Digit) -> Bool:
  match d:
    case D0{}: False{}
    case D1{}: False{}
    case D2{}: False{}
    case D3{}: False{}
    case D4{}: False{}
    case D5{}: True{}
    case D6{}: True{}
    case D7{}: True{}
    case D8{}: True{}
    case D9{}: True{}

def next_digit(d: Digit, bit: Bool) -> Digit:
  match d bit:
    case D0{} False{}: D0{}
    case D0{} True{}: D1{}
    case D1{} False{}: D2{}
    case D1{} True{}: D3{}
    case D2{} False{}: D4{}
    case D2{} True{}: D5{}
    case D3{} False{}: D6{}
    case D3{} True{}: D7{}
    case D4{} False{}: D8{}
    case D4{} True{}: D9{}
    case D5{} False{}: D0{}
    case D5{} True{}: D1{}
    case D6{} False{}: D2{}
    case D6{} True{}: D3{}
    case D7{} False{}: D4{}
    case D7{} True{}: D5{}
    case D8{} False{}: D6{}
    case D8{} True{}: D7{}
    case D9{} False{}: D8{}
    case D9{} True{}: D9{}

def place(b: Bool, n: Nat) -> Nat:
  match b:
    case False{}: Nat.double(n)
    case True{}: 1n+Nat.double(n)

law digit_word_measure:
  for +d: Digit
  {U32.to_nat(digit_word(d)) == digit_nat(d) : Nat}
def digit_word_measure(d):
  match d:
    case D0{}: {==}
    case D1{}: {==}
    case D2{}: {==}
    case D3{}: {==}
    case D4{}: {==}
    case D5{}: {==}
    case D6{}: {==}
    case D7{}: {==}
    case D8{}: {==}
    case D9{}: {==}

law digit_character_exact:
  for +d: Digit
  {Chr{U32.add(48, digit_word(d))} == digit_char(d) : Char}
def digit_character_exact(d):
  match d:
    case D0{}: {==}
    case D1{}: {==}
    case D2{}: {==}
    case D3{}: {==}
    case D4{}: {==}
    case D5{}: {==}
    case D6{}: {==}
    case D7{}: {==}
    case D8{}: {==}
    case D9{}: {==}

# Only twenty concrete remainder/input-bit states are possible. The quotient
# prefix is arbitrary; no quotient/remainder behavior is assumed.
law actual_division_step:
  for -n: Nat
  for +q: Word(n)
  for +d: Digit
  for +bit: Bool
  {U32.divmod.go.rec(n, bit, 10, (q, digit_word(d))) ==
    (WCon{quotient_bit(d), q}, digit_word(next_digit(d, bit))) : Word(1n+n) & U32}
def actual_division_step(n, q, d, bit):
  match d bit:
    case D0{} False{}: {==}
    case D0{} True{}: {==}
    case D1{} False{}: {==}
    case D1{} True{}: {==}
    case D2{} False{}: {==}
    case D2{} True{}: {==}
    case D3{} False{}: {==}
    case D3{} True{}: {==}
    case D4{} False{}: {==}
    case D4{} True{}: {==}
    case D5{} False{}: {==}
    case D5{} True{}: {==}
    case D6{} False{}: {==}
    case D6{} True{}: {==}
    case D7{} False{}: {==}
    case D7{} True{}: {==}
    case D8{} False{}: {==}
    case D8{} True{}: {==}
    case D9{} False{}: {==}
    case D9{} True{}: {==}

# Each closed digit/bit base is arithmetic over 0..19. Induction over the
# unbounded quotient adds twenty to both sides, so every quotient is covered.
law division_step_arithmetic:
  for +d: Digit
  for +bit: Bool
  for +q: Nat
  {place(bit, Nat.add(Nat.mul(q, 10n), digit_nat(d))) ==
    Nat.add(Nat.mul(place(quotient_bit(d), q), 10n), digit_nat(next_digit(d, bit))) : Nat}
def division_step_arithmetic(d, bit, q):
  match d bit:
    case D0{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 0n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 0n),
            division_step_arithmetic(D0{}, False{}, p))
    case D0{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 0n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 1n),
            division_step_arithmetic(D0{}, True{}, p))
    case D1{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 1n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 2n),
            division_step_arithmetic(D1{}, False{}, p))
    case D1{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 1n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 3n),
            division_step_arithmetic(D1{}, True{}, p))
    case D2{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 2n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 4n),
            division_step_arithmetic(D2{}, False{}, p))
    case D2{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 2n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 5n),
            division_step_arithmetic(D2{}, True{}, p))
    case D3{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 3n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 6n),
            division_step_arithmetic(D3{}, False{}, p))
    case D3{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 3n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 7n),
            division_step_arithmetic(D3{}, True{}, p))
    case D4{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 4n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 8n),
            division_step_arithmetic(D4{}, False{}, p))
    case D4{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 4n)),
            Nat.add(Nat.mul(place(False{}, p), 10n), 9n),
            division_step_arithmetic(D4{}, True{}, p))
    case D5{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 5n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 0n),
            division_step_arithmetic(D5{}, False{}, p))
    case D5{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 5n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 1n),
            division_step_arithmetic(D5{}, True{}, p))
    case D6{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 6n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 2n),
            division_step_arithmetic(D6{}, False{}, p))
    case D6{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 6n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 3n),
            division_step_arithmetic(D6{}, True{}, p))
    case D7{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 7n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 4n),
            division_step_arithmetic(D7{}, False{}, p))
    case D7{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 7n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 5n),
            division_step_arithmetic(D7{}, True{}, p))
    case D8{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 8n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 6n),
            division_step_arithmetic(D8{}, False{}, p))
    case D8{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 8n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 7n),
            division_step_arithmetic(D8{}, True{}, p))
    case D9{} False{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(False{}, Nat.add(Nat.mul(p, 10n), 9n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 8n),
            division_step_arithmetic(D9{}, False{}, p))
    case D9{} True{}:
      match q:
        case 0n: {==}
        case 1n+p:
          Equal.cong(Nat, Nat, v => 20n+v,
            place(True{}, Nat.add(Nat.mul(p, 10n), 9n)),
            Nat.add(Nat.mul(place(True{}, p), 10n), 9n),
            division_step_arithmetic(D9{}, True{}, p))

law word_bit_measure:
  for -n: Nat
  for +bit: Bool
  for +w: Word(n)
  {Word.to_nat(1n+n, WCon{bit, w}) == place(bit, Word.to_nat(n, w)) : Nat}
def word_bit_measure(n, bit, w):
  match bit:
    case False{}: {==}
    case True{}: {==}

# The actual algorithm produces these values; the equation is independent
# unbounded arithmetic and Digit witnesses the strict remainder range 0..9.
type Division<-n: Nat, -input: Word(n)> is Type:
  Division{quotient: Word(n), remainder: Digit,
    actual: {U32.divmod.go(n, input, 10) == (quotient, digit_word(remainder)) : Word(n) & U32},
    arithmetic: {Word.to_nat(n, input) == Nat.add(Nat.mul(Word.to_nat(n, quotient), 10n), digit_nat(remainder)) : Nat}}

def division_step(n: Nat, +bit: Bool, +hi: Word(n), proof: Division<n, hi>) -> Division<1n+n, WCon{bit, hi}>:
  match proof:
    case Division{+q, +d, actual, arithmetic}:
      Division{WCon{quotient_bit(d), q}, next_digit(d, bit),
        Equal.trans(Word(1n+n) & U32, U32.divmod.go.rec(n, bit, 10, U32.divmod.go(n, hi, 10)),
          U32.divmod.go.rec(n, bit, 10, (q, digit_word(d))),
          (WCon{quotient_bit(d), q}, digit_word(next_digit(d, bit))),
          Equal.cong(Word(n) & U32, Word(1n+n) & U32, qr => U32.divmod.go.rec(n, bit, 10, qr),
            U32.divmod.go(n, hi, 10), (q, digit_word(d)), actual), actual_division_step(n, q, d, bit)),
        Equal.trans(Nat, Word.to_nat(1n+n, WCon{bit, hi}), place(bit, Word.to_nat(n, hi)),
          Nat.add(Nat.mul(Word.to_nat(1n+n, WCon{quotient_bit(d), q}), 10n), digit_nat(next_digit(d, bit))),
          word_bit_measure(n, bit, hi),
          Equal.trans(Nat, place(bit, Word.to_nat(n, hi)),
            place(bit, Nat.add(Nat.mul(Word.to_nat(n, q), 10n), digit_nat(d))),
            Nat.add(Nat.mul(Word.to_nat(1n+n, WCon{quotient_bit(d), q}), 10n), digit_nat(next_digit(d, bit))),
            Equal.cong(Nat, Nat, v => place(bit, v), Word.to_nat(n, hi),
              Nat.add(Nat.mul(Word.to_nat(n, q), 10n), digit_nat(d)), arithmetic),
            Equal.trans(Nat, place(bit, Nat.add(Nat.mul(Word.to_nat(n, q), 10n), digit_nat(d))),
              Nat.add(Nat.mul(place(quotient_bit(d), Word.to_nat(n, q)), 10n), digit_nat(next_digit(d, bit))),
              Nat.add(Nat.mul(Word.to_nat(1n+n, WCon{quotient_bit(d), q}), 10n), digit_nat(next_digit(d, bit))),
              division_step_arithmetic(d, bit, Word.to_nat(n, q)),
              Equal.cong(Nat, Nat, v => Nat.add(Nat.mul(v, 10n), digit_nat(next_digit(d, bit))),
                place(quotient_bit(d), Word.to_nat(n, q)), Word.to_nat(1n+n, WCon{quotient_bit(d), q}),
                Equal.sym(Nat, Word.to_nat(1n+n, WCon{quotient_bit(d), q}), place(quotient_bit(d), Word.to_nat(n, q)), word_bit_measure(n, quotient_bit(d), q))))))}

law actual_division_by_ten:
  for +n: Nat
  for +input: Word(n)
  Division<n, input>
def actual_division_by_ten(n, input):
  match n:
    case 0n:
      match input:
        case WNil{}: Division{WNil{}, D0{}, {==}, {==}}
    case 1n+p:
      match input:
        case WCon{bit, +hi}:
          division_step(p, bit, hi, actual_division_by_ten(p, hi))

law remainder_is_decimal_digit:
  for +d: Digit
  {U32.is_lt(digit_word(d), 10) == True{} : Bool}
def remainder_is_decimal_digit(d):
  match d:
    case D0{}: {==}
    case D1{}: {==}
    case D2{}: {==}
    case D3{}: {==}
    case D4{}: {==}
    case D5{}: {==}
    case D6{}: {==}
    case D7{}: {==}
    case D8{}: {==}
    case D9{}: {==}

type U32Division<-input: U32> is Type:
  U32Division{quotient: U32, remainder: Digit,
    divided: {U32.div(input, 10) == quotient : U32},
    reduced: {U32.mod(input, 10) == digit_word(remainder) : U32},
    arithmetic: {U32.to_nat(input) == Nat.add(Nat.mul(U32.to_nat(quotient), 10n), digit_nat(remainder)) : Nat}}

def word_division(+input: Word(32n), proof: Division<32n, input>) -> U32Division<U32{input}>:
  match proof:
    case Division{+q, +d, +actual, arithmetic}:
      U32Division{U32{q}, d,
        Equal.cong(Word(32n) & U32, U32, U32.div.fin, U32.divmod.go(32n, input, 10), (q, digit_word(d)), actual),
        Equal.cong(Word(32n) & U32, U32, U32.mod.fin, U32.divmod.go(32n, input, 10), (q, digit_word(d)), actual), arithmetic}

law actual_u32_division_by_ten:
  for +input: U32
  U32Division<input>
def actual_u32_division_by_ten(input):
  match input:
    case U32{+w}: word_division(w, actual_division_by_ten(32n, w))
