import Base

# The pure controller's effect protocol, also consumed by Effects.drive.
# Constructor arities are deliberately distinct for the native interpreter.
type Task<-A: Type> is Type:
  Exchange{bytes: List<&2,U32>, next: List<&2,U32> -> A}
  Stop{code: U32}
