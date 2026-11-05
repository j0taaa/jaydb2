# Variable-length dynamic records; output actual contents, not cardinalities.
import Base
import ../../native/effects.bend as N
import ../../contract/Data.bend as D
import ../../library/Sequence.bend as Q
import ../../library/SortProof.bend as P
import ../../library/Relation.bend as J

def item(+key:U32,id:U32) -> D.Value:
  D.VRecord{"completed",D.VBool{U32.is_eq(U32.mod(key,2),1)},D.VRecord{"key",D.VInt{0,key},D.VRecord{"serial",D.VInt{0,id},D.VRecordEmpty{}}}}

def key(v:D.Value) -> U32:
  match v:
    case D.VRecord{"completed",b,D.VRecord{"key",D.VInt{0,k},rest}}: k
    case _: 255

def serial(v:D.Value) -> U32:
  match v:
    case D.VRecord{"completed",b,D.VRecord{"key",k,D.VRecord{"serial",D.VInt{0,i},rest}}}: i
    case _: 255

def less(a:D.Value,b:D.Value) -> Bool:
  U32.is_lt(key(a),key(b))

def join_key(v:D.Value) -> String:
  U32.show(key(v))

type Parsed is Data:
  Parsed{items:List<&2,D.Value>,rest:List<&2,U32>}

def prepend(x:D.Value,p:Parsed) -> Parsed:
  Parsed{xs,rest} = p
  Parsed{Con{x,xs},rest}

def read(n:Nat,xs:List<&2,U32>) -> Parsed:
  match n xs:
    case Succ{m} Con{k,Con{i,rest}}: prepend(item(k,i),read(m,rest))
    case _ xs: Parsed{Nil{},xs}

def append(xs:List<&2,U32>,ys:List<&2,U32>) -> List<&2,U32>:
  match xs:
    case Nil{}: ys
    case Con{x,rest}: Con{x,append(rest,ys)}

def length(xs:List<&2,D.Value>) -> U32:
  match xs:
    case Nil{}: 0
    case Con{x,rest}: U32.inc(length(rest))

def size(+n:U32) -> List<&2,U32>:
  [U32.and(n,255),U32.div(n,256)]

def items(xs:List<&2,D.Value>) -> List<&2,U32>:
  match xs:
    case Nil{}: Nil{}
    case Con{+x,rest}: Con{key(x),Con{serial(x),items(rest)}}

def pairs(xs:List<&2,D.Value>) -> List<&2,U32>:
  match xs:
    case Nil{}: Nil{}
    case Con{D.VList{+a,D.VList{+b,D.VListEmpty{}}},rest}:
      Con{key(a),Con{serial(a),Con{key(b),Con{serial(b),pairs(rest)}}}}
    case _: [254]

def key_number(s:Maybe<&2,U32>) -> U32:
  match s:
    case None{}: 254
    case Some{k}: k

def group_length(xs:List<&2,Q.Group>) -> U32:
  match xs:
    case Nil{}: 0
    case Con{x,rest}: U32.inc(group_length(rest))

def groups(xs:List<&2,Q.Group>) -> List<&2,U32>:
  match xs:
    case Nil{}: Nil{}
    case Con{Q.Group{k,+xs},rest}: Con{key_number(U32.read(k)),append(size(length(xs)),append(items(xs),groups(rest)))}

def output_items(+xs:List<&2,D.Value>) -> List<&2,U32>:
  append(size(length(xs)),items(xs))

def output_pairs(+xs:List<&2,D.Value>) -> List<&2,U32>:
  append(size(length(xs)),pairs(xs))

def output_groups(+xs:List<&2,Q.Group>) -> List<&2,U32>:
  append(size(group_length(xs)),groups(xs))

def operation(op:U32,+left:List<&2,D.Value>,+right:List<&2,D.Value>) -> List<&2,U32>:
  match op:
    case 0: output_items(Q.sort(~less,left))
    case 1: output_items(Q.sort(~P.completed_less,left))
    case 2: output_pairs(J.inner(~join_key,~join_key,left,right))
    case 3: output_pairs(J.left_join(~join_key,~join_key,left,right))
    case 4: output_groups(Q.group(~join_key,left))
    case _: [253]

def right(op:U32,left:List<&2,D.Value>,p:Parsed) -> List<&2,U32>:
  Parsed{xs,rest}=p
  operation(op,left,xs)

def left(op:U32,m:Nat,p:Parsed) -> List<&2,U32>:
  Parsed{xs,rest}=p
  right(op,xs,read(m,rest))

def run(input:List<&2,U32>) -> List<&2,U32>:
  match input:
    case Con{op,Con{n,Con{m,rest}}}: left(op,U32.to_nat(m),read(U32.to_nat(n),rest))
    case _: [252]

def main() -> IO(Unit):
  do IO<Unit>:
    input:List<&2,U32> <- N.read()
    N.write(run(input))
