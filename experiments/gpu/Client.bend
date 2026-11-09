import Base
import ./Data.bend as D
import ./Semantics.bend as S

# A balanced reduction with deterministic U32 work at each leaf.
def leaf(n: Nat, +x: U32) -> U32:
  match n:
    case 0n: x
    case 1n+p: leaf(p, (U32.xor(x, U32.div(x, 65536)) * 1664525 + 1013904223 : U32))

def tree(+depth: Nat, +seed: U32) -> U32:
  match depth:
    case 0n: leaf(64n, seed)
    case 1n+p:
      a b = tree(p, (seed * 2 : U32)) tree(p, (seed * 2 + 1 : U32))
      (a + b : U32)

# Credential text length is a runtime input, including on prepared calls.
def compute(value: D.Value) -> D.Value:
  match value:
    case D.VText{text}: D.VInt{0, tree!(String.length(text), 0)}
    case _: D.VAbsent{}

def respond(cancel: Bool, r: S.Return) -> S.Action:
  match cancel:
    case True{}: S.Refuse{D.VText{"cancelled"}}
    case False{}:
      match r:
        case S.Datum{D.Cell{value}}: S.Finish{compute(value)}
        case _: S.Refuse{D.VAbsent{}}

def read(id: String, cancel: Bool) -> S.Action:
  S.Access{D.ReadCell{D.Users{}, id, "credential"}, respond(cancel)}

def write(+id: String, value: String, cancel: Bool) -> S.Action:
  S.Access{D.DefineColumn{D.Users{}, id, "credential", D.VText{value}},
    unit => read(id, cancel)}

def arguments(id: String, args: D.Value) -> S.Action:
  match args:
    case D.VText{value}: write(id, value, False{})
    case _: write(id, "discarded", True{})

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  arguments(id, args)

def program() -> S.Program:
  S.Program{start}
