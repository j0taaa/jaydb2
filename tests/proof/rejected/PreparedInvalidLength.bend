# A declared zero-byte body cannot justify receiving actual extension bytes.
import Base
import ../../../contract/Resources.bend as X

law false:
  X.ReceptionValid(X.BodyReceived{0, 0, [7, 1]})
def false():
  {==}
