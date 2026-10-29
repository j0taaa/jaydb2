import Base

# Trusted kernel interface only. Applications do not import this file.
# The backend implements these constructors, ignoring foreign request snippets.
def read() -> IO(List<&2, U32>):
  import "./effects.c"

def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"

# Logical protocol stage; no clock or physical resource budget is attached.
def enter(etapa: U32) -> IO(Unit):
  import "./effects.c"

type Iteracao<-A: Type> is Type:
  Continuar{estado: A}
  Preparar{estado: A}
  Encerrar{bytes: List<&2, U32>}
  Inconsistente{}

def loop(-A: Type, step: A -> Iteracao<A>, initial: A) -> IO(Unit):
  import "./effects.c"
