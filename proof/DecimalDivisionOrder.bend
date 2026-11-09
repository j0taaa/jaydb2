# Actual divide-by-ten monotonicity, independent of decimal digit bounds.
# The remainder/input-bit state space is finite and checked exhaustively;
# quotient prefixes and word widths remain arbitrary.
import Base
import ./Foundations.bend as F
import ./Orders.bend as O
import ./DecimalDivision.bend as D

law equal_quotient_step_order:
  for +a: D.Digit
  for +b: D.Digit
  for +left_bit: Bool
  for +right_bit: Bool
  {Word.cmp.fin(left_bit, right_bit, U32.cmp(D.digit_word(a), D.digit_word(b))) ==
    O.priority(Bool.cmp(D.quotient_bit(a), D.quotient_bit(b)),
      U32.cmp(D.digit_word(D.next_digit(a, left_bit)), D.digit_word(D.next_digit(b, right_bit)))) : Cmp}
def equal_quotient_step_order(a, b, left_bit, right_bit):
  match a b left_bit right_bit:
    case D.D0{} D.D0{} False{} False{}: {==}
    case D.D0{} D.D0{} False{} True{}: {==}
    case D.D0{} D.D0{} True{} False{}: {==}
    case D.D0{} D.D0{} True{} True{}: {==}
    case D.D0{} D.D1{} False{} False{}: {==}
    case D.D0{} D.D1{} False{} True{}: {==}
    case D.D0{} D.D1{} True{} False{}: {==}
    case D.D0{} D.D1{} True{} True{}: {==}
    case D.D0{} D.D2{} False{} False{}: {==}
    case D.D0{} D.D2{} False{} True{}: {==}
    case D.D0{} D.D2{} True{} False{}: {==}
    case D.D0{} D.D2{} True{} True{}: {==}
    case D.D0{} D.D3{} False{} False{}: {==}
    case D.D0{} D.D3{} False{} True{}: {==}
    case D.D0{} D.D3{} True{} False{}: {==}
    case D.D0{} D.D3{} True{} True{}: {==}
    case D.D0{} D.D4{} False{} False{}: {==}
    case D.D0{} D.D4{} False{} True{}: {==}
    case D.D0{} D.D4{} True{} False{}: {==}
    case D.D0{} D.D4{} True{} True{}: {==}
    case D.D0{} D.D5{} False{} False{}: {==}
    case D.D0{} D.D5{} False{} True{}: {==}
    case D.D0{} D.D5{} True{} False{}: {==}
    case D.D0{} D.D5{} True{} True{}: {==}
    case D.D0{} D.D6{} False{} False{}: {==}
    case D.D0{} D.D6{} False{} True{}: {==}
    case D.D0{} D.D6{} True{} False{}: {==}
    case D.D0{} D.D6{} True{} True{}: {==}
    case D.D0{} D.D7{} False{} False{}: {==}
    case D.D0{} D.D7{} False{} True{}: {==}
    case D.D0{} D.D7{} True{} False{}: {==}
    case D.D0{} D.D7{} True{} True{}: {==}
    case D.D0{} D.D8{} False{} False{}: {==}
    case D.D0{} D.D8{} False{} True{}: {==}
    case D.D0{} D.D8{} True{} False{}: {==}
    case D.D0{} D.D8{} True{} True{}: {==}
    case D.D0{} D.D9{} False{} False{}: {==}
    case D.D0{} D.D9{} False{} True{}: {==}
    case D.D0{} D.D9{} True{} False{}: {==}
    case D.D0{} D.D9{} True{} True{}: {==}
    case D.D1{} D.D0{} False{} False{}: {==}
    case D.D1{} D.D0{} False{} True{}: {==}
    case D.D1{} D.D0{} True{} False{}: {==}
    case D.D1{} D.D0{} True{} True{}: {==}
    case D.D1{} D.D1{} False{} False{}: {==}
    case D.D1{} D.D1{} False{} True{}: {==}
    case D.D1{} D.D1{} True{} False{}: {==}
    case D.D1{} D.D1{} True{} True{}: {==}
    case D.D1{} D.D2{} False{} False{}: {==}
    case D.D1{} D.D2{} False{} True{}: {==}
    case D.D1{} D.D2{} True{} False{}: {==}
    case D.D1{} D.D2{} True{} True{}: {==}
    case D.D1{} D.D3{} False{} False{}: {==}
    case D.D1{} D.D3{} False{} True{}: {==}
    case D.D1{} D.D3{} True{} False{}: {==}
    case D.D1{} D.D3{} True{} True{}: {==}
    case D.D1{} D.D4{} False{} False{}: {==}
    case D.D1{} D.D4{} False{} True{}: {==}
    case D.D1{} D.D4{} True{} False{}: {==}
    case D.D1{} D.D4{} True{} True{}: {==}
    case D.D1{} D.D5{} False{} False{}: {==}
    case D.D1{} D.D5{} False{} True{}: {==}
    case D.D1{} D.D5{} True{} False{}: {==}
    case D.D1{} D.D5{} True{} True{}: {==}
    case D.D1{} D.D6{} False{} False{}: {==}
    case D.D1{} D.D6{} False{} True{}: {==}
    case D.D1{} D.D6{} True{} False{}: {==}
    case D.D1{} D.D6{} True{} True{}: {==}
    case D.D1{} D.D7{} False{} False{}: {==}
    case D.D1{} D.D7{} False{} True{}: {==}
    case D.D1{} D.D7{} True{} False{}: {==}
    case D.D1{} D.D7{} True{} True{}: {==}
    case D.D1{} D.D8{} False{} False{}: {==}
    case D.D1{} D.D8{} False{} True{}: {==}
    case D.D1{} D.D8{} True{} False{}: {==}
    case D.D1{} D.D8{} True{} True{}: {==}
    case D.D1{} D.D9{} False{} False{}: {==}
    case D.D1{} D.D9{} False{} True{}: {==}
    case D.D1{} D.D9{} True{} False{}: {==}
    case D.D1{} D.D9{} True{} True{}: {==}
    case D.D2{} D.D0{} False{} False{}: {==}
    case D.D2{} D.D0{} False{} True{}: {==}
    case D.D2{} D.D0{} True{} False{}: {==}
    case D.D2{} D.D0{} True{} True{}: {==}
    case D.D2{} D.D1{} False{} False{}: {==}
    case D.D2{} D.D1{} False{} True{}: {==}
    case D.D2{} D.D1{} True{} False{}: {==}
    case D.D2{} D.D1{} True{} True{}: {==}
    case D.D2{} D.D2{} False{} False{}: {==}
    case D.D2{} D.D2{} False{} True{}: {==}
    case D.D2{} D.D2{} True{} False{}: {==}
    case D.D2{} D.D2{} True{} True{}: {==}
    case D.D2{} D.D3{} False{} False{}: {==}
    case D.D2{} D.D3{} False{} True{}: {==}
    case D.D2{} D.D3{} True{} False{}: {==}
    case D.D2{} D.D3{} True{} True{}: {==}
    case D.D2{} D.D4{} False{} False{}: {==}
    case D.D2{} D.D4{} False{} True{}: {==}
    case D.D2{} D.D4{} True{} False{}: {==}
    case D.D2{} D.D4{} True{} True{}: {==}
    case D.D2{} D.D5{} False{} False{}: {==}
    case D.D2{} D.D5{} False{} True{}: {==}
    case D.D2{} D.D5{} True{} False{}: {==}
    case D.D2{} D.D5{} True{} True{}: {==}
    case D.D2{} D.D6{} False{} False{}: {==}
    case D.D2{} D.D6{} False{} True{}: {==}
    case D.D2{} D.D6{} True{} False{}: {==}
    case D.D2{} D.D6{} True{} True{}: {==}
    case D.D2{} D.D7{} False{} False{}: {==}
    case D.D2{} D.D7{} False{} True{}: {==}
    case D.D2{} D.D7{} True{} False{}: {==}
    case D.D2{} D.D7{} True{} True{}: {==}
    case D.D2{} D.D8{} False{} False{}: {==}
    case D.D2{} D.D8{} False{} True{}: {==}
    case D.D2{} D.D8{} True{} False{}: {==}
    case D.D2{} D.D8{} True{} True{}: {==}
    case D.D2{} D.D9{} False{} False{}: {==}
    case D.D2{} D.D9{} False{} True{}: {==}
    case D.D2{} D.D9{} True{} False{}: {==}
    case D.D2{} D.D9{} True{} True{}: {==}
    case D.D3{} D.D0{} False{} False{}: {==}
    case D.D3{} D.D0{} False{} True{}: {==}
    case D.D3{} D.D0{} True{} False{}: {==}
    case D.D3{} D.D0{} True{} True{}: {==}
    case D.D3{} D.D1{} False{} False{}: {==}
    case D.D3{} D.D1{} False{} True{}: {==}
    case D.D3{} D.D1{} True{} False{}: {==}
    case D.D3{} D.D1{} True{} True{}: {==}
    case D.D3{} D.D2{} False{} False{}: {==}
    case D.D3{} D.D2{} False{} True{}: {==}
    case D.D3{} D.D2{} True{} False{}: {==}
    case D.D3{} D.D2{} True{} True{}: {==}
    case D.D3{} D.D3{} False{} False{}: {==}
    case D.D3{} D.D3{} False{} True{}: {==}
    case D.D3{} D.D3{} True{} False{}: {==}
    case D.D3{} D.D3{} True{} True{}: {==}
    case D.D3{} D.D4{} False{} False{}: {==}
    case D.D3{} D.D4{} False{} True{}: {==}
    case D.D3{} D.D4{} True{} False{}: {==}
    case D.D3{} D.D4{} True{} True{}: {==}
    case D.D3{} D.D5{} False{} False{}: {==}
    case D.D3{} D.D5{} False{} True{}: {==}
    case D.D3{} D.D5{} True{} False{}: {==}
    case D.D3{} D.D5{} True{} True{}: {==}
    case D.D3{} D.D6{} False{} False{}: {==}
    case D.D3{} D.D6{} False{} True{}: {==}
    case D.D3{} D.D6{} True{} False{}: {==}
    case D.D3{} D.D6{} True{} True{}: {==}
    case D.D3{} D.D7{} False{} False{}: {==}
    case D.D3{} D.D7{} False{} True{}: {==}
    case D.D3{} D.D7{} True{} False{}: {==}
    case D.D3{} D.D7{} True{} True{}: {==}
    case D.D3{} D.D8{} False{} False{}: {==}
    case D.D3{} D.D8{} False{} True{}: {==}
    case D.D3{} D.D8{} True{} False{}: {==}
    case D.D3{} D.D8{} True{} True{}: {==}
    case D.D3{} D.D9{} False{} False{}: {==}
    case D.D3{} D.D9{} False{} True{}: {==}
    case D.D3{} D.D9{} True{} False{}: {==}
    case D.D3{} D.D9{} True{} True{}: {==}
    case D.D4{} D.D0{} False{} False{}: {==}
    case D.D4{} D.D0{} False{} True{}: {==}
    case D.D4{} D.D0{} True{} False{}: {==}
    case D.D4{} D.D0{} True{} True{}: {==}
    case D.D4{} D.D1{} False{} False{}: {==}
    case D.D4{} D.D1{} False{} True{}: {==}
    case D.D4{} D.D1{} True{} False{}: {==}
    case D.D4{} D.D1{} True{} True{}: {==}
    case D.D4{} D.D2{} False{} False{}: {==}
    case D.D4{} D.D2{} False{} True{}: {==}
    case D.D4{} D.D2{} True{} False{}: {==}
    case D.D4{} D.D2{} True{} True{}: {==}
    case D.D4{} D.D3{} False{} False{}: {==}
    case D.D4{} D.D3{} False{} True{}: {==}
    case D.D4{} D.D3{} True{} False{}: {==}
    case D.D4{} D.D3{} True{} True{}: {==}
    case D.D4{} D.D4{} False{} False{}: {==}
    case D.D4{} D.D4{} False{} True{}: {==}
    case D.D4{} D.D4{} True{} False{}: {==}
    case D.D4{} D.D4{} True{} True{}: {==}
    case D.D4{} D.D5{} False{} False{}: {==}
    case D.D4{} D.D5{} False{} True{}: {==}
    case D.D4{} D.D5{} True{} False{}: {==}
    case D.D4{} D.D5{} True{} True{}: {==}
    case D.D4{} D.D6{} False{} False{}: {==}
    case D.D4{} D.D6{} False{} True{}: {==}
    case D.D4{} D.D6{} True{} False{}: {==}
    case D.D4{} D.D6{} True{} True{}: {==}
    case D.D4{} D.D7{} False{} False{}: {==}
    case D.D4{} D.D7{} False{} True{}: {==}
    case D.D4{} D.D7{} True{} False{}: {==}
    case D.D4{} D.D7{} True{} True{}: {==}
    case D.D4{} D.D8{} False{} False{}: {==}
    case D.D4{} D.D8{} False{} True{}: {==}
    case D.D4{} D.D8{} True{} False{}: {==}
    case D.D4{} D.D8{} True{} True{}: {==}
    case D.D4{} D.D9{} False{} False{}: {==}
    case D.D4{} D.D9{} False{} True{}: {==}
    case D.D4{} D.D9{} True{} False{}: {==}
    case D.D4{} D.D9{} True{} True{}: {==}
    case D.D5{} D.D0{} False{} False{}: {==}
    case D.D5{} D.D0{} False{} True{}: {==}
    case D.D5{} D.D0{} True{} False{}: {==}
    case D.D5{} D.D0{} True{} True{}: {==}
    case D.D5{} D.D1{} False{} False{}: {==}
    case D.D5{} D.D1{} False{} True{}: {==}
    case D.D5{} D.D1{} True{} False{}: {==}
    case D.D5{} D.D1{} True{} True{}: {==}
    case D.D5{} D.D2{} False{} False{}: {==}
    case D.D5{} D.D2{} False{} True{}: {==}
    case D.D5{} D.D2{} True{} False{}: {==}
    case D.D5{} D.D2{} True{} True{}: {==}
    case D.D5{} D.D3{} False{} False{}: {==}
    case D.D5{} D.D3{} False{} True{}: {==}
    case D.D5{} D.D3{} True{} False{}: {==}
    case D.D5{} D.D3{} True{} True{}: {==}
    case D.D5{} D.D4{} False{} False{}: {==}
    case D.D5{} D.D4{} False{} True{}: {==}
    case D.D5{} D.D4{} True{} False{}: {==}
    case D.D5{} D.D4{} True{} True{}: {==}
    case D.D5{} D.D5{} False{} False{}: {==}
    case D.D5{} D.D5{} False{} True{}: {==}
    case D.D5{} D.D5{} True{} False{}: {==}
    case D.D5{} D.D5{} True{} True{}: {==}
    case D.D5{} D.D6{} False{} False{}: {==}
    case D.D5{} D.D6{} False{} True{}: {==}
    case D.D5{} D.D6{} True{} False{}: {==}
    case D.D5{} D.D6{} True{} True{}: {==}
    case D.D5{} D.D7{} False{} False{}: {==}
    case D.D5{} D.D7{} False{} True{}: {==}
    case D.D5{} D.D7{} True{} False{}: {==}
    case D.D5{} D.D7{} True{} True{}: {==}
    case D.D5{} D.D8{} False{} False{}: {==}
    case D.D5{} D.D8{} False{} True{}: {==}
    case D.D5{} D.D8{} True{} False{}: {==}
    case D.D5{} D.D8{} True{} True{}: {==}
    case D.D5{} D.D9{} False{} False{}: {==}
    case D.D5{} D.D9{} False{} True{}: {==}
    case D.D5{} D.D9{} True{} False{}: {==}
    case D.D5{} D.D9{} True{} True{}: {==}
    case D.D6{} D.D0{} False{} False{}: {==}
    case D.D6{} D.D0{} False{} True{}: {==}
    case D.D6{} D.D0{} True{} False{}: {==}
    case D.D6{} D.D0{} True{} True{}: {==}
    case D.D6{} D.D1{} False{} False{}: {==}
    case D.D6{} D.D1{} False{} True{}: {==}
    case D.D6{} D.D1{} True{} False{}: {==}
    case D.D6{} D.D1{} True{} True{}: {==}
    case D.D6{} D.D2{} False{} False{}: {==}
    case D.D6{} D.D2{} False{} True{}: {==}
    case D.D6{} D.D2{} True{} False{}: {==}
    case D.D6{} D.D2{} True{} True{}: {==}
    case D.D6{} D.D3{} False{} False{}: {==}
    case D.D6{} D.D3{} False{} True{}: {==}
    case D.D6{} D.D3{} True{} False{}: {==}
    case D.D6{} D.D3{} True{} True{}: {==}
    case D.D6{} D.D4{} False{} False{}: {==}
    case D.D6{} D.D4{} False{} True{}: {==}
    case D.D6{} D.D4{} True{} False{}: {==}
    case D.D6{} D.D4{} True{} True{}: {==}
    case D.D6{} D.D5{} False{} False{}: {==}
    case D.D6{} D.D5{} False{} True{}: {==}
    case D.D6{} D.D5{} True{} False{}: {==}
    case D.D6{} D.D5{} True{} True{}: {==}
    case D.D6{} D.D6{} False{} False{}: {==}
    case D.D6{} D.D6{} False{} True{}: {==}
    case D.D6{} D.D6{} True{} False{}: {==}
    case D.D6{} D.D6{} True{} True{}: {==}
    case D.D6{} D.D7{} False{} False{}: {==}
    case D.D6{} D.D7{} False{} True{}: {==}
    case D.D6{} D.D7{} True{} False{}: {==}
    case D.D6{} D.D7{} True{} True{}: {==}
    case D.D6{} D.D8{} False{} False{}: {==}
    case D.D6{} D.D8{} False{} True{}: {==}
    case D.D6{} D.D8{} True{} False{}: {==}
    case D.D6{} D.D8{} True{} True{}: {==}
    case D.D6{} D.D9{} False{} False{}: {==}
    case D.D6{} D.D9{} False{} True{}: {==}
    case D.D6{} D.D9{} True{} False{}: {==}
    case D.D6{} D.D9{} True{} True{}: {==}
    case D.D7{} D.D0{} False{} False{}: {==}
    case D.D7{} D.D0{} False{} True{}: {==}
    case D.D7{} D.D0{} True{} False{}: {==}
    case D.D7{} D.D0{} True{} True{}: {==}
    case D.D7{} D.D1{} False{} False{}: {==}
    case D.D7{} D.D1{} False{} True{}: {==}
    case D.D7{} D.D1{} True{} False{}: {==}
    case D.D7{} D.D1{} True{} True{}: {==}
    case D.D7{} D.D2{} False{} False{}: {==}
    case D.D7{} D.D2{} False{} True{}: {==}
    case D.D7{} D.D2{} True{} False{}: {==}
    case D.D7{} D.D2{} True{} True{}: {==}
    case D.D7{} D.D3{} False{} False{}: {==}
    case D.D7{} D.D3{} False{} True{}: {==}
    case D.D7{} D.D3{} True{} False{}: {==}
    case D.D7{} D.D3{} True{} True{}: {==}
    case D.D7{} D.D4{} False{} False{}: {==}
    case D.D7{} D.D4{} False{} True{}: {==}
    case D.D7{} D.D4{} True{} False{}: {==}
    case D.D7{} D.D4{} True{} True{}: {==}
    case D.D7{} D.D5{} False{} False{}: {==}
    case D.D7{} D.D5{} False{} True{}: {==}
    case D.D7{} D.D5{} True{} False{}: {==}
    case D.D7{} D.D5{} True{} True{}: {==}
    case D.D7{} D.D6{} False{} False{}: {==}
    case D.D7{} D.D6{} False{} True{}: {==}
    case D.D7{} D.D6{} True{} False{}: {==}
    case D.D7{} D.D6{} True{} True{}: {==}
    case D.D7{} D.D7{} False{} False{}: {==}
    case D.D7{} D.D7{} False{} True{}: {==}
    case D.D7{} D.D7{} True{} False{}: {==}
    case D.D7{} D.D7{} True{} True{}: {==}
    case D.D7{} D.D8{} False{} False{}: {==}
    case D.D7{} D.D8{} False{} True{}: {==}
    case D.D7{} D.D8{} True{} False{}: {==}
    case D.D7{} D.D8{} True{} True{}: {==}
    case D.D7{} D.D9{} False{} False{}: {==}
    case D.D7{} D.D9{} False{} True{}: {==}
    case D.D7{} D.D9{} True{} False{}: {==}
    case D.D7{} D.D9{} True{} True{}: {==}
    case D.D8{} D.D0{} False{} False{}: {==}
    case D.D8{} D.D0{} False{} True{}: {==}
    case D.D8{} D.D0{} True{} False{}: {==}
    case D.D8{} D.D0{} True{} True{}: {==}
    case D.D8{} D.D1{} False{} False{}: {==}
    case D.D8{} D.D1{} False{} True{}: {==}
    case D.D8{} D.D1{} True{} False{}: {==}
    case D.D8{} D.D1{} True{} True{}: {==}
    case D.D8{} D.D2{} False{} False{}: {==}
    case D.D8{} D.D2{} False{} True{}: {==}
    case D.D8{} D.D2{} True{} False{}: {==}
    case D.D8{} D.D2{} True{} True{}: {==}
    case D.D8{} D.D3{} False{} False{}: {==}
    case D.D8{} D.D3{} False{} True{}: {==}
    case D.D8{} D.D3{} True{} False{}: {==}
    case D.D8{} D.D3{} True{} True{}: {==}
    case D.D8{} D.D4{} False{} False{}: {==}
    case D.D8{} D.D4{} False{} True{}: {==}
    case D.D8{} D.D4{} True{} False{}: {==}
    case D.D8{} D.D4{} True{} True{}: {==}
    case D.D8{} D.D5{} False{} False{}: {==}
    case D.D8{} D.D5{} False{} True{}: {==}
    case D.D8{} D.D5{} True{} False{}: {==}
    case D.D8{} D.D5{} True{} True{}: {==}
    case D.D8{} D.D6{} False{} False{}: {==}
    case D.D8{} D.D6{} False{} True{}: {==}
    case D.D8{} D.D6{} True{} False{}: {==}
    case D.D8{} D.D6{} True{} True{}: {==}
    case D.D8{} D.D7{} False{} False{}: {==}
    case D.D8{} D.D7{} False{} True{}: {==}
    case D.D8{} D.D7{} True{} False{}: {==}
    case D.D8{} D.D7{} True{} True{}: {==}
    case D.D8{} D.D8{} False{} False{}: {==}
    case D.D8{} D.D8{} False{} True{}: {==}
    case D.D8{} D.D8{} True{} False{}: {==}
    case D.D8{} D.D8{} True{} True{}: {==}
    case D.D8{} D.D9{} False{} False{}: {==}
    case D.D8{} D.D9{} False{} True{}: {==}
    case D.D8{} D.D9{} True{} False{}: {==}
    case D.D8{} D.D9{} True{} True{}: {==}
    case D.D9{} D.D0{} False{} False{}: {==}
    case D.D9{} D.D0{} False{} True{}: {==}
    case D.D9{} D.D0{} True{} False{}: {==}
    case D.D9{} D.D0{} True{} True{}: {==}
    case D.D9{} D.D1{} False{} False{}: {==}
    case D.D9{} D.D1{} False{} True{}: {==}
    case D.D9{} D.D1{} True{} False{}: {==}
    case D.D9{} D.D1{} True{} True{}: {==}
    case D.D9{} D.D2{} False{} False{}: {==}
    case D.D9{} D.D2{} False{} True{}: {==}
    case D.D9{} D.D2{} True{} False{}: {==}
    case D.D9{} D.D2{} True{} True{}: {==}
    case D.D9{} D.D3{} False{} False{}: {==}
    case D.D9{} D.D3{} False{} True{}: {==}
    case D.D9{} D.D3{} True{} False{}: {==}
    case D.D9{} D.D3{} True{} True{}: {==}
    case D.D9{} D.D4{} False{} False{}: {==}
    case D.D9{} D.D4{} False{} True{}: {==}
    case D.D9{} D.D4{} True{} False{}: {==}
    case D.D9{} D.D4{} True{} True{}: {==}
    case D.D9{} D.D5{} False{} False{}: {==}
    case D.D9{} D.D5{} False{} True{}: {==}
    case D.D9{} D.D5{} True{} False{}: {==}
    case D.D9{} D.D5{} True{} True{}: {==}
    case D.D9{} D.D6{} False{} False{}: {==}
    case D.D9{} D.D6{} False{} True{}: {==}
    case D.D9{} D.D6{} True{} False{}: {==}
    case D.D9{} D.D6{} True{} True{}: {==}
    case D.D9{} D.D7{} False{} False{}: {==}
    case D.D9{} D.D7{} False{} True{}: {==}
    case D.D9{} D.D7{} True{} False{}: {==}
    case D.D9{} D.D7{} True{} True{}: {==}
    case D.D9{} D.D8{} False{} False{}: {==}
    case D.D9{} D.D8{} False{} True{}: {==}
    case D.D9{} D.D8{} True{} False{}: {==}
    case D.D9{} D.D8{} True{} True{}: {==}
    case D.D9{} D.D9{} False{} False{}: {==}
    case D.D9{} D.D9{} False{} True{}: {==}
    case D.D9{} D.D9{} True{} False{}: {==}
    case D.D9{} D.D9{} True{} True{}: {==}

law division_step_order:
  for quotient_order: Cmp
  for +a: D.Digit
  for +b: D.Digit
  for +left_bit: Bool
  for +right_bit: Bool
  {Word.cmp.fin(left_bit, right_bit,
      O.priority(quotient_order, U32.cmp(D.digit_word(a), D.digit_word(b)))) ==
    O.priority(Word.cmp.fin(D.quotient_bit(a), D.quotient_bit(b), quotient_order),
      U32.cmp(D.digit_word(D.next_digit(a, left_bit)), D.digit_word(D.next_digit(b, right_bit)))) : Cmp}
def division_step_order(quotient_order, a, b, left_bit, right_bit):
  match quotient_order:
    case LT{}: {==}
    case EQ{}: equal_quotient_step_order(a, b, left_bit, right_bit)
    case GT{}: {==}

# Both quotient/remainder pairs are equations of the real pinned Base routine.
# The comparison invariant is established, never received as a premise.
type PairedDivision<-n: Nat, -left: Word(n), -right: Word(n)> is Type:
  PairedDivision{left_quotient: Word(n), right_quotient: Word(n),
    left_remainder: D.Digit, right_remainder: D.Digit,
    left_actual: {U32.divmod.go(n, left, 10) ==
      (left_quotient, D.digit_word(left_remainder)) : Word(n) & U32},
    right_actual: {U32.divmod.go(n, right, 10) ==
      (right_quotient, D.digit_word(right_remainder)) : Word(n) & U32},
    order: {Word.cmp(n, left, right) == O.priority(Word.cmp(n, left_quotient, right_quotient),
      U32.cmp(D.digit_word(left_remainder), D.digit_word(right_remainder))) : Cmp}}

def paired_step(+n: Nat, +left_bit: Bool, +right_bit: Bool,
  +left: Word(n), +right: Word(n), previous: PairedDivision<n, left, right>) ->
  PairedDivision<1n+n, WCon{left_bit, left}, WCon{right_bit, right}>:
  match previous:
    case PairedDivision{+lq, +rq, +ld, +rd, actual_left, actual_right, ordered}:
      PairedDivision{WCon{D.quotient_bit(ld), lq}, WCon{D.quotient_bit(rd), rq},
        D.next_digit(ld, left_bit), D.next_digit(rd, right_bit),
        Equal.trans(Word(1n+n) & U32,
          U32.divmod.go.rec(n, left_bit, 10, U32.divmod.go(n, left, 10)),
          U32.divmod.go.rec(n, left_bit, 10, (lq, D.digit_word(ld))),
          (WCon{D.quotient_bit(ld), lq}, D.digit_word(D.next_digit(ld, left_bit))),
          Equal.cong(Word(n) & U32, Word(1n+n) & U32,
            pair => U32.divmod.go.rec(n, left_bit, 10, pair),
            U32.divmod.go(n, left, 10), (lq, D.digit_word(ld)), actual_left),
          D.actual_division_step(n, lq, ld, left_bit)),
        Equal.trans(Word(1n+n) & U32,
          U32.divmod.go.rec(n, right_bit, 10, U32.divmod.go(n, right, 10)),
          U32.divmod.go.rec(n, right_bit, 10, (rq, D.digit_word(rd))),
          (WCon{D.quotient_bit(rd), rq}, D.digit_word(D.next_digit(rd, right_bit))),
          Equal.cong(Word(n) & U32, Word(1n+n) & U32,
            pair => U32.divmod.go.rec(n, right_bit, 10, pair),
            U32.divmod.go(n, right, 10), (rq, D.digit_word(rd)), actual_right),
          D.actual_division_step(n, rq, rd, right_bit)),
        Equal.trans(Cmp,
          Word.cmp.fin(left_bit, right_bit, Word.cmp(n, left, right)),
          Word.cmp.fin(left_bit, right_bit, O.priority(Word.cmp(n, lq, rq),
            U32.cmp(D.digit_word(ld), D.digit_word(rd)))),
          O.priority(Word.cmp(1n+n, WCon{D.quotient_bit(ld), lq}, WCon{D.quotient_bit(rd), rq}),
            U32.cmp(D.digit_word(D.next_digit(ld, left_bit)), D.digit_word(D.next_digit(rd, right_bit)))),
          Equal.cong(Cmp, Cmp, order => Word.cmp.fin(left_bit, right_bit, order),
            Word.cmp(n, left, right), O.priority(Word.cmp(n, lq, rq),
              U32.cmp(D.digit_word(ld), D.digit_word(rd))), ordered),
          division_step_order(Word.cmp(n, lq, rq), ld, rd, left_bit, right_bit))}

law actual_paired_division_order:
  for +n: Nat
  for +left: Word(n)
  for +right: Word(n)
  PairedDivision<n, left, right>
def actual_paired_division_order(n, left, right):
  match n:
    case 0n:
      match left right:
        case WNil{} WNil{}:
          PairedDivision{WNil{}, WNil{}, D.D0{}, D.D0{}, {==}, {==}, {==}}
    case 1n+p:
      match left right:
        case WCon{lb, +lt} WCon{rb, +rt}:
          paired_step(p, lb, rb, lt, rt, actual_paired_division_order(p, lt, rt))

law priority_le_implies_quotient_le:
  for quotient_order: Cmp
  for -remainder_order: Cmp
  for bounded: {Cmp.is_le(O.priority(quotient_order, remainder_order)) == True{} : Bool}
  {Cmp.is_le(quotient_order) == True{} : Bool}
def priority_le_implies_quotient_le(quotient_order, remainder_order, bounded):
  match quotient_order:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: F.absurd_boolean({False{} == True{} : Bool}, bounded)

def compared_quotient_is_le(-input_order: Cmp, +quotient_order: Cmp, -remainder_order: Cmp,
  order: {input_order == O.priority(quotient_order, remainder_order) : Cmp},
  bounded: {Cmp.is_le(input_order) == True{} : Bool}) ->
  {Cmp.is_le(quotient_order) == True{} : Bool}:
  priority_le_implies_quotient_le(quotient_order, remainder_order,
    (%order : {Cmp.is_le(_) == True{} : Bool} bounded))

def u32_order_from_pair(+left: Word(32n), +right: Word(32n),
  paired: PairedDivision<32n, left, right>,
  bounded: {U32.is_le(U32{left}, U32{right}) == True{} : Bool}) ->
  {U32.is_le(U32.div(U32{left}, 10), U32.div(U32{right}, 10)) == True{} : Bool}:
  match paired:
    case PairedDivision{+lq, +rq, ld, rd, actual_left, actual_right, ordered}:
      %Equal.sym(Word(32n) & U32, U32.divmod.go(32n, left, 10),
        (lq, D.digit_word(ld)), actual_left) :
        {U32.is_le(U32.div.fin(_), U32.div.fin(U32.divmod.go(32n, right, 10))) == True{} : Bool}
      %Equal.sym(Word(32n) & U32, U32.divmod.go(32n, right, 10),
        (rq, D.digit_word(rd)), actual_right) :
        {U32.is_le(U32{lq}, U32.div.fin(_)) == True{} : Bool}
      compared_quotient_is_le(Word.cmp(32n, left, right), Word.cmp(32n, lq, rq),
        U32.cmp(D.digit_word(ld), D.digit_word(rd)), ordered, bounded)

law actual_u32_divide_ten_monotone:
  for +a: U32
  for +b: U32
  for less: {U32.is_le(a, b) == True{} : Bool}
  {U32.is_le(U32.div(a, 10), U32.div(b, 10)) == True{} : Bool}
def actual_u32_divide_ten_monotone(a, b, less):
  match a b:
    case U32{+aw} U32{+bw}:
      u32_order_from_pair(aw, bw, actual_paired_division_order(32n, aw, bw), less)
