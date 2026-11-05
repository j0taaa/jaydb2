import Base

type Task<-A: Type> is Type:
  Exchange{bytes: List<&2, U32>, next: List<&2, U32> -> A}
  Stop{code: U32}

def drive(-A: Type, step: A -> Task<A>, initial: A) -> IO(Unit):
  import "./effects.c"
