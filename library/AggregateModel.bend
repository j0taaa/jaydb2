# Independent unbounded integer/list interpretation for checked aggregation.
# Equality is explicitly Data equality of natural cross-sums, so copying it
# never assumes that an arbitrary Type certificate can be duplicated.
import Base
import ./Value.bend as V
import ./Int64Proofs.bend as A
import ./Int64IntegerProduct.bend as P
import ./Int64IntegerAddition.bend as Add

type Both<-left: Data,-right: Data> is Data:
  Both{left: left,right: right}

def EqualInteger(a: A.Integer,b: A.Integer) -> Data:
  A.Integer{ap,an}=a
  A.Integer{bp,bn}=b
  {Nat.add(ap,bn) == Nat.add(bp,an) : Nat}

law equality_to_integer_product_model:
  for +a: A.Integer
  for +b: A.Integer
  for exact: EqualInteger(a,b)
  P.IntegerEqual(a,b)
def equality_to_integer_product_model(a,b,exact):
  match a b:
    case A.Integer{ap,an} A.Integer{bp,bn}: exact

law equality_from_integer_product_model:
  for +a: A.Integer
  for +b: A.Integer
  for exact: P.IntegerEqual(a,b)
  EqualInteger(a,b)
def equality_from_integer_product_model(a,b,exact):
  match a b:
    case A.Integer{ap,an} A.Integer{bp,bn}: exact

def sum(xs: List<&2,V.Int64>) -> A.Integer:
  match xs:
    case Nil{}: A.Integer{0n,0n}
    case Con{x,tail}: Add.add(A.integer(x),sum(tail))

def length(xs: List<&2,V.Int64>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{x,tail}: 1n+length(tail)

type Representable<-integer: A.Integer> is Data:
  Representable{word: V.Int64,exact: EqualInteger(A.integer(word),integer)}

# Every nonempty right-hand suffix has an ordinary representable integer sum.
# The empty suffix is zero and is always representable.
def SuffixSumsFit(xs: List<&2,V.Int64>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{+x,+tail}: Both<Representable<sum(Con{x,tail})>,SuffixSumsFit(tail)>

law empty_sum_is_representable:
  Representable<sum(Nil{})>
def empty_sum_is_representable():
  Representable{V.Int64{0,0},{==}}
