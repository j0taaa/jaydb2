import Base
import ../../../src/Termination.bend as T
import ../GpuPrograms.bend as GPU

# One access plus the bang terminal action needs depth two, as in finite_read.
law false:
  T.Finite(1n, GPU.read("bob"))
def false(): r => Unit{}
