# Nine divisions cannot exhaust every U32; the ten-digit bound is necessary.
import Base
import ../../../proof/DecimalQuotients.bend as Q

law false_nine_steps_exhaust_maximum:
  {Q.quotient_after(9n, 4294967295) == 0 : U32}
def false_nine_steps_exhaust_maximum():
  {==}
