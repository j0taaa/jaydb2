# A declared zero-byte body cannot justify receiving actual extension bytes.
import Base
import ../../../contract/Resources.bend as X

law false_mismatched_physical_length_is_valid:
  X.ReceptionValid(X.BodyReceived{0, 0, [7, 1]})
def false_mismatched_physical_length_is_valid():
  {==}
