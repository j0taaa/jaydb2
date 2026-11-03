import Base
import ../../../contract/Bytes.bend as B
import ../../../src/Codec.bend as C
import ../../../proof/AllocationLengths.bend as A

law false:
  {A.in_construction(C.open_checked(C.Short{}, C.TextValue{}, B.Number64{0, 1}, C.Root{})) == True{} : Bool}
def false():
  {==}
