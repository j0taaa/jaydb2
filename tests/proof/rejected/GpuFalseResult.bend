import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../GpuPrograms.bend as GPU

# A bang does not make a false result certificate admissible.
law false:
  {GPU.finish(7) == S.Finish{D.VInt{0, 9}} : S.Action}
def false(): {==}
