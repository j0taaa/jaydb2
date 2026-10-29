import Base
import ../../../native/effects.bend as Native

def read_b(xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, tail}:
      read_b(tail, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(x, 48))))

def read_a(xs: List<&2, U32>, acc: Nat) -> Nat & Nat:
  match xs:
    case Nil{}:
      (acc, 0n)
    case Con{255, tail}:
      (acc, read_b(tail, 0n))
    case Con{x, tail}:
      read_a(tail, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(x, 48))))

def order(c: Cmp) -> String:
  match c:
    case LT{}:
      "<"
    case EQ{}:
      "="
    case GT{}:
      ">"

def pattern(n: Nat) -> String:
  match n:
    case 0n:
      "zero"
    case 1n:
      "one"
    case 2n:
      "two"
    case 3n+p:
      Nat.show(p)

def qr(pair: Nat & Nat) -> String:
  (q, r) = pair
  String.append(Nat.show(q), String.append(":", Nat.show(r)))

def identity(-A: Type, value: A) -> A:
  value

def apply(f: Nat -> Nat, value: Nat) -> Nat:
  f(value)

def operation(op: U32, a: Nat, b: Nat) -> String:
  match op:
    case 0:
      Nat.show(Nat.add(a, b))
    case 1:
      Nat.show(Nat.sub(a, b))
    case 2:
      Nat.show(Nat.mul(a, b))
    case 3:
      Nat.show(Nat.div(a, b))
    case 4:
      Nat.show(Nat.mod(a, b))
    case 5:
      qr(Nat.divmod(a, b))
    case 6:
      order(Nat.cmp(a, b))
    case 7:
      pattern(identity(Nat, a))
    case 8:
      Nat.show(Nat.pow(a, b))
    case 9:
      Nat.show(Nat.min(a, b))
    case 10:
      Nat.show(Nat.max(a, b))
    case 11:
      U32.show(U32.from_nat(a))
    case 12:
      U32.show(U32.pow(U32.from_nat(a), b))
    case 13:
      U32.show(U32.shln(U32.from_nat(a), b))
    case 14:
      U32.show(U32.shrn(U32.from_nat(a), b))
    case 15:
      Nat.show(apply(Nat.add(a), b))
    case other:
      "unknown"

def evaluate(op: U32, args: Nat & Nat) -> String:
  (a, b) = args
  operation(op, a, b)

def run(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "empty"
    case Con{op, rest}:
      evaluate(op, read_a(rest, 0n))

def ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{x}, tail}:
      Con{x, ascii(tail)}

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(ascii(run(bytes)))
