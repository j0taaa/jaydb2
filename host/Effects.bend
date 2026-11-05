import Base
import ./Tasks.bend as T

def drive(-A: Type, step: A -> T.Task<A>, initial: A) -> IO(Unit):
  import "./effects.c"
