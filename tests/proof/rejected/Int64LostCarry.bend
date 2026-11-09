# Dropping the low-word carry cannot inherit the actual arithmetic theorem.
import Base
import ../../../library/Value.bend as V
import ../../../library/Int64Proofs.bend as P

def wrong_add(a: V.Int64, b: V.Int64) -> V.Int64:
  V.Int64{h, l} = a
  V.Int64{i, j} = b
  V.Int64{U32.add(h, i), U32.add(l, j)}

law false_add_without_carry:
  for +a: V.Int64
  for +b: V.Int64
  {P.bits(wrong_add(a, b)) == Word.add(64n, P.bits(a), P.bits(b)) : Word(64n)}
def false_add_without_carry(a, b):
  P.wrapping_add_is_full_word_add(a, b)
