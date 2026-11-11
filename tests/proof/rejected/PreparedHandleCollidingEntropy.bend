# The repeated entropy candidate is already registered; fallback cannot reuse it.
import Base
import ../../../proof/HandleAllocation.bend as A
import ../../../proof/HandleHex.bend as H

law false:
  {A.native_allocate(Word.zero(256n), [H.counter_key(0n)]) ==
    Some{H.counter_key(0n)} : Maybe<&2, String>}
def false():
  {==}
