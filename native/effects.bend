import Base

# Trusted kernel interface only. Applications do not import this file.
# Implemented by the accompanying application C effects through the official API.
def read() -> IO(List<&2, U32>):
  import "./effects.c"

def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"

type Iteration<-A: Type> is Type:
  Continue{state: A}
  Prepare{state: A}
  FinishOutput{bytes: List<&2, U32>}
  Inconsistent{}

def loop(-A: Type, step: A -> Iteration<A>, initial: A) -> IO(Unit):
  import "./effects.c"
