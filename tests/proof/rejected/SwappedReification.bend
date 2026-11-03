import Base
import ../../../contract/Data.bend as D
import ../../../src/Reification.bend as R

law false:
  {R.arguments(R.text([3, 0, 0, 0, 0, 0, 0, 0, 1]), 0, 9) == D.VInt{0, 2} : D.Value}
def false():
  {==}
