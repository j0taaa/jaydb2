# Flooring creates plateaus; monotonicity does not imply strict increase.
import Base
import ../../../proof/DecimalDivisionOrder.bend as O

law false_divide_ten_is_strict_on_every_increase:
  {U32.is_lt(U32.div(0, 10), U32.div(9, 10)) == True{} : Bool}
def false_divide_ten_is_strict_on_every_increase():
  {==}
