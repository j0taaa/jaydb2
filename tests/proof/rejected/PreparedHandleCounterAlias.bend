# Distinct real counters cannot share their fixed-width canonical encoding.
import Base
import ../../../proof/HandleHex.bend as H

law false:
  {H.counter_key(0n) == H.counter_key(1n) : String}
def false():
  {==}
