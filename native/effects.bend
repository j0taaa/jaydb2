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

type Incoming<-A: Type> is Type:
  RequestFrame{bytes: List<&2, U32>}
  ReplyFrame{pending: A, bytes: List<&2, U32>}

type Exchange<-A: Type> is Type:
  AskFrame{bytes: List<&2, U32>, pending: A}
  FinalFrame{bytes: List<&2, U32>}
  InvalidFrame{}

def serve(-A: Type, step: Incoming<A> -> Exchange<A>, single: Bool) -> IO(Unit):
  import "./effects.c"
