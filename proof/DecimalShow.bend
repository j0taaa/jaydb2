# Source-token reification for the ACTUAL pinned Base U32.show implementation.
import Base
import ../contract/Logic.bend as L
import ./DecimalDivision.bend as D
import ./DecimalParser.bend as P
import ./DecimalQuotients.bend as Q
import ./Foundations.bend as F
import ./CodecCounters.bend as Counts

def Nonempty(xs: List<&2, D.Digit>) -> Type:
  match xs:
    case Nil{}: Empty
    case Con{h, rest}: Unit

law appended_digit_nonempty:
  for xs: List<&2, D.Digit>
  for d: D.Digit
  Nonempty(P.append(xs, [d]))
def appended_digit_nonempty(xs, d):
  match xs:
    case Nil{}: Unit{}
    case Con{h, rest}: Unit{}

law string_append_associative:
  for a: String
  for +b: String
  for +c: String
  {(a ++ b) ++ c == a ++ (b ++ c) : String}
def string_append_associative(a, b, c):
  match a:
    case SNil{}: {==}
    case SCon{+h, rest}:
      Equal.cong(String, String, s => SCon{h, s},
        (rest ++ b) ++ c, rest ++ (b ++ c), string_append_associative(rest, b, c))

law string_append_empty:
  for +s: String
  {s ++ "" == s : String}
def string_append_empty(s):
  match s:
    case SNil{}: {==}
    case SCon{+h, +rest}:
      Equal.cong(String, String, s => SCon{h, s}, rest ++ "", rest, string_append_empty(rest))

law appended_digit_rendering:
  for +xs: List<&2, D.Digit>
  for +d: D.Digit
  for +accumulator: String
  {P.render(P.append(xs, [d])) ++ accumulator == P.render(xs) ++ SCon{D.digit_char(d), accumulator} : String}
def appended_digit_rendering(xs, d, accumulator):
  Equal.trans(String, P.render(P.append(xs, [d])) ++ accumulator,
    (P.render(xs) ++ P.render([d])) ++ accumulator, P.render(xs) ++ SCon{D.digit_char(d), accumulator},
    Equal.cong(String, String, s => s ++ accumulator, P.render(P.append(xs, [d])),
      P.render(xs) ++ P.render([d]), P.rendered_append(xs, [d])),
    string_append_associative(P.render(xs), P.render([d]), accumulator))

# The accumulator is arbitrary source text, and the actual show loop prepends
# precisely the proved decimal digits. No source equality is a premise.
type Displayed<-steps: Nat, -number: U32, -accumulator: String> is Type:
  Displayed{digits: List<&2, D.Digit>,
    shown: {U32.show.go(steps, number, accumulator) == P.render(digits) ++ accumulator : String},
    numeric: {P.value(digits) == U32.to_nat(number) : Nat},
    nonzero: {U32.is_zero(number) == False{} : Bool} -> Nonempty(digits)}

law actual_show_step:
  for +steps: Nat
  for +number: U32
  for +quotient: U32
  for +digit: D.Digit
  for +accumulator: String
  for zero: {U32.is_zero(number) == False{} : Bool}
  for divided: {U32.div(number, 10) == quotient : U32}
  for reduced: {U32.mod(number, 10) == D.digit_word(digit) : U32}
  {U32.show.go(1n+steps, number, accumulator) == U32.show.go(steps, quotient, SCon{D.digit_char(digit), accumulator}) : String}
def actual_show_step(steps, number, quotient, digit, accumulator, zero, divided, reduced):
  %Equal.sym(Bool, U32.is_zero(number), False{}, zero) :
    {U32.show.fin(steps, accumulator, number, _) == U32.show.go(steps, quotient, SCon{D.digit_char(digit), accumulator}) : String}
  %Equal.sym(U32, U32.div(number, 10), quotient, divided) :
    {U32.show.go(steps, _, SCon{Chr{U32.add(48, U32.mod(number, 10))}, accumulator}) ==
      U32.show.go(steps, quotient, SCon{D.digit_char(digit), accumulator}) : String}
  %Equal.sym(U32, U32.mod(number, 10), D.digit_word(digit), reduced) :
    {U32.show.go(steps, quotient, SCon{Chr{U32.add(48, _)}, accumulator}) ==
      U32.show.go(steps, quotient, SCon{D.digit_char(digit), accumulator}) : String}
  Equal.cong(Char, String, c => U32.show.go(steps, quotient, SCon{c, accumulator}),
    Chr{U32.add(48, D.digit_word(digit))}, D.digit_char(digit), D.digit_character_exact(digit))

def after_recursive(+steps: Nat, +number: U32, +quotient: U32, +digit: D.Digit, +accumulator: String,
  zero: {U32.is_zero(number) == False{} : Bool},
  divided: {U32.div(number, 10) == quotient : U32},
  reduced: {U32.mod(number, 10) == D.digit_word(digit) : U32},
  arithmetic: {U32.to_nat(number) == Nat.add(Nat.mul(U32.to_nat(quotient), 10n), D.digit_nat(digit)) : Nat},
  recursive: Displayed<steps, quotient, SCon{D.digit_char(digit), accumulator}>) -> Displayed<1n+steps, number, accumulator>:
  match recursive:
    case Displayed{+xs, shown, numeric, nonzero}:
      Displayed{P.append(xs, [digit]),
        Equal.trans(String, U32.show.go(1n+steps, number, accumulator),
          U32.show.go(steps, quotient, SCon{D.digit_char(digit), accumulator}), P.render(P.append(xs, [digit])) ++ accumulator,
          actual_show_step(steps, number, quotient, digit, accumulator, zero, divided, reduced),
          Equal.trans(String, U32.show.go(steps, quotient, SCon{D.digit_char(digit), accumulator}),
            P.render(xs) ++ SCon{D.digit_char(digit), accumulator}, P.render(P.append(xs, [digit])) ++ accumulator, shown,
            Equal.sym(String, P.render(P.append(xs, [digit])) ++ accumulator,
              P.render(xs) ++ SCon{D.digit_char(digit), accumulator}, appended_digit_rendering(xs, digit, accumulator)))),
        Equal.trans(Nat, P.value(P.append(xs, [digit])), Nat.add(Nat.mul(P.value(xs), 10n), D.digit_nat(digit)), U32.to_nat(number),
          P.appended_digit_value(xs, digit),
          Equal.trans(Nat, Nat.add(Nat.mul(P.value(xs), 10n), D.digit_nat(digit)),
            Nat.add(Nat.mul(U32.to_nat(quotient), 10n), D.digit_nat(digit)), U32.to_nat(number),
            Equal.cong(Nat, Nat, n => Nat.add(Nat.mul(n, 10n), D.digit_nat(digit)), P.value(xs), U32.to_nat(quotient), numeric),
            Equal.sym(Nat, U32.to_nat(number), Nat.add(Nat.mul(U32.to_nat(quotient), 10n), D.digit_nat(digit)), arithmetic))),
        ignored => appended_digit_nonempty(xs, digit)}

def after_division(+steps: Nat, +number: U32, +accumulator: String,
  exhausted: {Q.quotient_after(1n+steps, number) == 0 : U32},
  zero: {U32.is_zero(number) == False{} : Bool}, division: D.U32Division<number>,
  next: @q: U32 -> @acc: String -> {Q.quotient_after(steps, q) == 0 : U32} -> Displayed<steps, q, acc>) -> Displayed<1n+steps, number, accumulator>:
  match division:
    case D.U32Division{+q, +digit, +divided, reduced, arithmetic}:
      after_recursive(steps, number, q, digit, accumulator, zero, divided, reduced, arithmetic,
        next(q, SCon{D.digit_char(digit), accumulator},
          (%divided : {Q.quotient_after(steps, _) == 0 : U32} exhausted)))

def zero_display(+steps: Nat, +number: U32, +accumulator: String,
  +same: {number == 0 : U32}, shown: {U32.show.go(steps, number, accumulator) == accumulator : String}) -> Displayed<steps, number, accumulator>:
  Displayed{Nil{}, shown,
    Equal.cong(U32, Nat, U32.to_nat, 0, number, Equal.sym(U32, number, 0, same)),
    nonzero => F.false_negative_true(Equal.trans(Bool, False{}, U32.is_zero(number), True{},
      Equal.sym(Bool, U32.is_zero(number), False{}, nonzero),
      Equal.cong(U32, Bool, U32.is_zero, number, 0, same)))}

law zero_show_stops:
  for steps: Nat
  for +number: U32
  for +accumulator: String
  for zero: {U32.is_zero(number) == True{} : Bool}
  {U32.show.go(1n+steps, number, accumulator) == accumulator : String}
def zero_show_stops(steps, number, accumulator, zero):
  %Equal.sym(Bool, U32.is_zero(number), True{}, zero) :
    {U32.show.fin(steps, accumulator, number, _) == accumulator : String}
  {==}

def show_case(+steps: Nat, +number: U32, +accumulator: String,
  exhausted: {Q.quotient_after(1n+steps, number) == 0 : U32}, zero: Bool,
  +checked: {U32.is_zero(number) == zero : Bool},
  next: @q: U32 -> @acc: String -> {Q.quotient_after(steps, q) == 0 : U32} -> Displayed<steps, q, acc>) -> Displayed<1n+steps, number, accumulator>:
  match zero:
    case True{}:
      zero_display(1n+steps, number, accumulator, Counts.equality_u32(number, 0, checked), zero_show_stops(steps, number, accumulator, checked))
    case False{}:
      after_division(steps, number, accumulator, exhausted, checked, D.actual_u32_division_by_ten(number), next)

law actual_show_loop_has_decimal_value:
  for +steps: Nat
  for +number: U32
  for +accumulator: String
  for exhausted: {Q.quotient_after(steps, number) == 0 : U32}
  Displayed<steps, number, accumulator>
def actual_show_loop_has_decimal_value(steps, number, accumulator, exhausted):
  match steps:
    case 0n: zero_display(0n, number, accumulator, exhausted, {==})
    case 1n+ +previous:
      show_case(previous, number, accumulator, exhausted, U32.is_zero(number), {==},
        q => acc => done => actual_show_loop_has_decimal_value(previous, q, acc, done))

type Decimal<-number: U32> is Type:
  Decimal{digits: List<&2, D.Digit>, shown: {U32.show(number) == P.render(digits) : String},
    numeric: {P.value(digits) == U32.to_nat(number) : Nat}, nonempty: Nonempty(digits)}

law nonzero_show_is_loop:
  for +number: U32
  for zero: {U32.is_zero(number) == False{} : Bool}
  {U32.show(number) == U32.show.go(10n, number, "") : String}
def nonzero_show_is_loop(number, zero):
  %Equal.sym(Bool, U32.is_zero(number), False{}, zero) : {U32.show.if(number, _) == U32.show.go(10n, number, "") : String}
  {==}

law zero_show_is_one_digit:
  for +number: U32
  for zero: {U32.is_zero(number) == True{} : Bool}
  {U32.show(number) == "0" : String}
def zero_show_is_one_digit(number, zero):
  %Equal.sym(Bool, U32.is_zero(number), True{}, zero) : {U32.show.if(number, _) == "0" : String}
  {==}

def nonzero_decimal(+number: U32, +zero: {U32.is_zero(number) == False{} : Bool}, displayed: Displayed<10n, number, "">) -> Decimal<number>:
  match displayed:
    case Displayed{+digits, shown, numeric, nonempty}:
      Decimal{digits,
        Equal.trans(String, U32.show(number), U32.show.go(10n, number, ""), P.render(digits), nonzero_show_is_loop(number, zero),
          Equal.trans(String, U32.show.go(10n, number, ""), P.render(digits) ++ "", P.render(digits), shown, string_append_empty(P.render(digits)))),
        numeric, nonempty(zero)}

def decimal_case(+number: U32, zero: Bool, +checked: {U32.is_zero(number) == zero : Bool}) -> Decimal<number>:
  match zero:
    case True{}:
      Decimal{[D.D0{}], zero_show_is_one_digit(number, checked),
        Equal.cong(U32, Nat, U32.to_nat, 0, number, Equal.sym(U32, number, 0, Counts.equality_u32(number, 0, checked))), Unit{}}
    case False{}:
      nonzero_decimal(number, checked,
        actual_show_loop_has_decimal_value(10n, number, "", Q.every_u32_is_exhausted_in_ten_steps(number)))

# No decimal-correctness or execution-success premise: this is the actual show.
law actual_u32_show_is_mathematical_decimal:
  for +number: U32
  Decimal<number>
def actual_u32_show_is_mathematical_decimal(number):
  decimal_case(number, U32.is_zero(number), {==})

def parsed_rendering(+head: D.Digit, +tail: List<&2, D.Digit>, +number: U32, +rest: String,
  boundary: P.Boundary<rest>, numeric: {P.value(Con{head, tail}) == U32.to_nat(number) : Nat}) ->
  {P.parse_word(P.render(Con{head, tail}) ++ rest) == P.WordParsed{number, rest} : P.WordParsed}:
  Equal.trans(P.WordParsed, P.parse_word(P.render(Con{head, tail}) ++ rest), P.word_result(P.Parsed{P.value(Con{head, tail}), rest}), P.WordParsed{number, rest},
    Equal.cong(P.Parsed, P.WordParsed, P.word_result, P.parse(P.render(Con{head, tail}) ++ rest), P.Parsed{P.value(Con{head, tail}), rest},
      P.parse_nonempty_rendered_digits(head, tail, rest, boundary)),
    Equal.trans(P.WordParsed, P.word_result(P.Parsed{P.value(Con{head, tail}), rest}), P.word_result(P.Parsed{U32.to_nat(number), rest}), P.WordParsed{number, rest},
      Equal.cong(Nat, P.WordParsed, value => P.word_result(P.Parsed{value, rest}), P.value(Con{head, tail}), U32.to_nat(number), numeric),
      P.parsed_exact_measure_recovers_word(number, rest)))

def from_decimal(+number: U32, +rest: String, boundary: P.Boundary<rest>, decimal: Decimal<number>) ->
  {P.parse_word(U32.show(number) ++ rest) == P.WordParsed{number, rest} : P.WordParsed}:
  match decimal:
    case Decimal{digits, shown, numeric, nonempty}:
      match digits:
        case Nil{}:
          L.ex_false({P.parse_word(U32.show(number) ++ rest) == P.WordParsed{number, rest} : P.WordParsed}, nonempty)
        case Con{+head, +tail}:
          Equal.trans(P.WordParsed, P.parse_word(U32.show(number) ++ rest), P.parse_word(P.render(Con{head, tail}) ++ rest), P.WordParsed{number, rest},
            Equal.cong(String, P.WordParsed, s => P.parse_word(s ++ rest), U32.show(number), P.render(Con{head, tail}), shown),
            parsed_rendering(head, tail, number, rest, boundary, numeric))

law actual_u32_show_recovers_exact_word_and_source_boundary:
  for +number: U32
  for +rest: String
  for boundary: P.Boundary<rest>
  {P.parse_word(U32.show(number) ++ rest) == P.WordParsed{number, rest} : P.WordParsed}
def actual_u32_show_recovers_exact_word_and_source_boundary(number, rest, boundary):
  from_decimal(number, rest, boundary, actual_u32_show_is_mathematical_decimal(number))
