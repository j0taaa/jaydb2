import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as A
import ../../../library/AggregateCountProofs.bend as C

# Every element contributes one, including the minimum signed64 value.
law false:
  {A.count([V.Int64{2147483648,0}]) == None{} : Maybe<&2,V.Int64>}
def false(): {==}
