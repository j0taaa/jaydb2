# Ignoring the low-word borrow cannot satisfy full-word subtraction.
import Base
import ../../../library/Int64SubProofs.bend as P
import ../../../library/Value.bend as V
import ../../../library/Int64Proofs.bend as A

def wrong_sub(a: V.Int64, b: V.Int64) -> V.Int64:
  V.Int64{h, l} = a
  V.Int64{i, j} = b
  V.Int64{U32.sub(h, i), U32.sub(l, j)}

law false:
  for +a: V.Int64
  for +b: V.Int64
  {A.bits(wrong_sub(a, b)) == Word.sub(64n, A.bits(a), A.bits(b)) : Word(64n)}
def false(a, b):
  P.wrapping_sub_is_full_word_sub(a, b)
