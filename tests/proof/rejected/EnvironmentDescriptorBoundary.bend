import Base
import ../../../proof/EnvironmentBinding.bend as E
import ../../../contract/Bytes.bend as B

law false_name_content_boundary_can_move:
  {E.descriptor([E.Sized{E.Entry{[65], [66, 67]}, B.Number64{0, 1}, B.Number64{0, 2}}]) ==
   E.descriptor([E.Sized{E.Entry{[65, 66], [67]}, B.Number64{0, 2}, B.Number64{0, 1}}]) : List<&2, U32>}
def false_name_content_boundary_can_move():
  {==}
