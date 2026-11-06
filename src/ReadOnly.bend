# Compatible implementation names for the fixed read-only contract predicate.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/ReadOnlyContract.bend as C

def Operation(o: D.Operation) -> Type:
  C.Operation(o)

def Prefix(n: Nat, a: S.Action) -> Type:
  C.Prefix(n, a)

def Action(n: Nat, a: S.Action) -> Type:
  C.Action(n, a)

def Program(-p: S.Program) -> Type:
  C.Program(p)
