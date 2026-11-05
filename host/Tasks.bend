import Base

# Generic effect description only; policy is in Controller and Policy.
type Task<-A: Type> is Type:
  Exchange{bytes: List<&2,U32>, next: List<&2,U32> -> A}
  Stop{code: U32}
