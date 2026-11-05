# Dynamic binary oracle fixture; not an application dependency.
import Base
import ../../native/effects.bend as N
import ../../library/Value.bend as V
import ../../library/Int64.bend as I

def bytes(x: U32) -> List<&2, U32>:
  +x = x
  [U32.and(x, 255), U32.and(U32.shrn(x, 8n), 255), U32.and(U32.shrn(x, 16n), 255), U32.shrn(x, 24n)]

def append(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}: ys
    case Con{x, rest}: Con{x, append(rest, ys)}

def output(x: V.Int64) -> List<&2, U32>:
  V.Int64{h, l} = x
  append(bytes(l), bytes(h))

def maybe(x: Maybe<&2, V.Int64>) -> List<&2, U32>:
  match x:
    case None{}: [0]
    case Some{x}: Con{1, output(x)}

def division(x: Maybe<&2, I.Division>) -> List<&2, U32>:
  match x:
    case None{}: [0]
    case Some{I.Division{q, r}}: Con{1, append(output(q), output(r))}

def word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.add(U32.add(a, U32.mul(b, 256)), U32.add(U32.mul(c, 65536), U32.mul(d, 16777216)))

def operation(op: U32, a: V.Int64, b: V.Int64) -> List<&2, U32>:
  match op:
    case 0: maybe(I.add(a, b))
    case 1: maybe(I.sub(a, b))
    case 2: maybe(I.mul(a, b))
    case 3: division(I.divmod(a, b))
    case 4: [Bool.to_u32(I.lt(a, b))]
    case _: [255]

def run(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{op, Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h,
      Con{i, Con{j, Con{k, Con{l, Con{m, Con{n, Con{o, Con{p, rest}}}}}}}}}}}}}}}}}:
      append(operation(op, V.Int64{word(e,f,g,h), word(a,b,c,d)}, V.Int64{word(m,n,o,p), word(i,j,k,l)}), run(rest))
    case _: Nil{}

def main() -> IO(Unit):
  do IO<Unit>:
    input : List<&2, U32> <- N.read()
    N.write(run(input))
