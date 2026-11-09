# Ten steps suffice by a proved global order bound, not input sampling.
import Base
import ./DecimalDivisionOrder.bend as Order
import ./CodecUTF8InverseBits.bend as Bits
import ./CodecWordsWord.bend as W

def quotient_after(steps: Nat, number: U32) -> U32:
  match steps:
    case 0n: number
    case 1n+p: quotient_after(p, U32.div(number, 10))

law quotient_iteration_monotone:
  for steps: Nat
  for +a: U32
  for +b: U32
  for less: {U32.is_le(a, b) == True{} : Bool}
  {U32.is_le(quotient_after(steps, a), quotient_after(steps, b)) == True{} : Bool}
def quotient_iteration_monotone(steps, a, b, less):
  match steps:
    case 0n: less
    case 1n+p:
      quotient_iteration_monotone(p, U32.div(a, 10), U32.div(b, 10),
        Order.actual_u32_divide_ten_monotone(a, b, less))

law maximum_word_is_exhausted_in_ten_steps:
  {quotient_after(10n, 4294967295) == 0 : U32}
def maximum_word_is_exhausted_in_ten_steps():
  {==}

law every_word_is_bounded_by_maximum:
  for +number: U32
  {U32.is_le(number, 4294967295) == True{} : Bool}
def every_word_is_bounded_by_maximum(number):
  match number:
    case U32{w}: Bits.word_less_equal_ones(32n, w)

law bounded_by_zero_is_zero:
  for +number: U32
  for less: {U32.is_le(number, 0) == True{} : Bool}
  {number == 0 : U32}
def bounded_by_zero_is_zero(number, less):
  match number:
    case U32{+w}:
      Equal.cong(Word(32n), U32, w => U32{w}, w, Word.zero(32n), W.word_until_zero(32n, w, less))

law every_u32_is_exhausted_in_ten_steps:
  for +number: U32
  {quotient_after(10n, number) == 0 : U32}
def every_u32_is_exhausted_in_ten_steps(number):
  bounded_by_zero_is_zero(quotient_after(10n, number),
    (%Equal.sym(U32, quotient_after(10n, 4294967295), 0, maximum_word_is_exhausted_in_ten_steps()) :
      {U32.is_le(quotient_after(10n, number), _) == True{} : Bool}
      quotient_iteration_monotone(10n, number, 4294967295, every_word_is_bounded_by_maximum(number))))
