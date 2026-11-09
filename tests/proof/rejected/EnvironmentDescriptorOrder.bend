import Base
import ../../../proof/EnvironmentBinding.bend as E
import ../../../contract/Bytes.bend as B

law false_descriptor_order_does_not_bind:
  {E.descriptor([E.Sized{E.Entry{[65], [0]}, B.Number64{0, 1}, B.Number64{0, 1}}, E.Sized{E.Entry{[66], [1]}, B.Number64{0, 1}, B.Number64{0, 1}}]) ==
   E.descriptor([E.Sized{E.Entry{[66], [1]}, B.Number64{0, 1}, B.Number64{0, 1}}, E.Sized{E.Entry{[65], [0]}, B.Number64{0, 1}, B.Number64{0, 1}}]) : List<&2, U32>}
def false_descriptor_order_does_not_bind():
  {==}
