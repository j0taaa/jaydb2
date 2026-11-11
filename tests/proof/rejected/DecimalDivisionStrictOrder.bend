# Flooring creates plateaus; monotonicity does not imply strict increase.
import Base
import ../../../proof/DecimalDivisionOrder.bend as O

law false:
  {U32.is_lt(U32.div(0, 10), U32.div(9, 10)) == True{} : Bool}
def false():
  {==}
