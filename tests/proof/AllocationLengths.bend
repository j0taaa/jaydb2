# Universal reapplication of the boundary to be connected to the native hook.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Logic.bend as L
import ../../src/Codec.bend as C
import ../../proof/AllocationLengths.bend as A

law field_variable_open_is_here_inside_of_two_limits:
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for variable: A.Variable(f)
  for opened: {A.in_construction(C.conclude_word(f, high, low, stack, body, ceiling)) == True{} : Bool}
  L.E<{C.less_equal64(B.Number64{high, low}, body) == True{} : Bool},
    {C.less_equal64(B.Number64{high, low}, ceiling) == True{} : Bool}>
def field_variable_open_is_here_inside_of_two_limits(f, high, low, stack, body, ceiling, variable, opened):
  A.opening_variable_real_respects_body_and_ceiling(f, high, low, stack, body, ceiling, variable, opened)

law none_check_insufficient_opens_field:
  for +c: C.Check
  for +f: C.Purpose
  for +q: B.Number64
  for +stack: C.Stack
  for opened: {A.in_construction(C.open_checked(c, f, q, stack)) == True{} : Bool}
  {c == C.Fits{} : C.Check}
def none_check_insufficient_opens_field(c, f, q, stack, opened):
  A.opening_in_construction_requires_check_real(c, f, q, stack, opened)
