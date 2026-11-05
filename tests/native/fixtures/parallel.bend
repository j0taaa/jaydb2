import Base
import ../../../native/effects.bend as Native

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

def run(bytes: List<&2, U32>) -> IO(Unit):
  match bytes:
    case Nil{}: Native.write([])
    case Con{depth, rest}:
      +result = tree!(U32.to_nat(depth), 0)
      Native.write([U32.and(result, 255), U32.and(U32.div(result, 256), 255),
        U32.and(U32.div(result, 65536), 255), U32.div(result, 16777216)])

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    run(bytes)
