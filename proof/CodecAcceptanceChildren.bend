# Child witnesses extracted from the parser, without assumed canonicity.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecAcceptancePrefix.bend as X
import ./CodecLimitsNames.bend as N
import ./CodecLimitsSequences.bend as S

type ChildRead<-v: D.Value, -bs: List<&2, U32>, -max: Nat> is Type:
  ChildRead{body: B.Number64, ceiling: B.Number64, outside: C.Stack,
    local: {R.machine(X.execute_local(bs, outside, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine},
    bound: {Nat.is_le(B.length(bs), max) == True{} : Bool}}

def ChildrenRead(xs: List<&2, S.ValueSegmented>, +max: Nat) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.ValueSegmented{v, bs}, t}:
      L.E<ChildRead<v, bs, max>, ChildrenRead(t, max)>

def BytesPositive(bs: List<&2, U32>) -> Type:
  match bs:
    case Nil{}:
      Empty
    case Con{b, t}:
      Unit

law tag_root_local_accepted_has_bytes:
  for +bs: List<&2, U32>
  for +outside: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {R.machine(X.execute_local(bs, outside, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
  BytesPositive(bs)
def tag_root_local_accepted_has_bytes(bs, outside, body, ceiling, v, accepted):
  match bs:
    case Nil{}:
      F.false_negative_true(Equal.cong(C.Machine, Bool, m => X.and_ready(m), C.Tag{C.Root{}}, C.DecodedReady{v}, accepted))
    case Con{b, t}:
      Unit{}

def limit_of_bytes_equal(+a: List<&2, U32>, +b: List<&2, U32>, +n: Nat,
  bytes: {a == b : List<&2, U32>}, limit: {Nat.is_le(B.length(a), n) == True{} : Bool}) ->
  {Nat.is_le(B.length(b), n) == True{} : Bool}:
  %bytes : {Nat.is_le(B.length(_), n) == True{} : Bool}
  limit

law limit_prefix:
  for +pre: List<&2, U32>
  for +suf: List<&2, U32>
  for +n: Nat
  for limit: {Nat.is_le(B.length(B.concatenate(pre, suf)), n) == True{} : Bool}
  {Nat.is_le(B.length(pre), n) == True{} : Bool}
def limit_prefix(pre, suf, n, limit):
  match pre n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{b, t} 0n:
      F.absurd_boolean({False{} == True{} : Bool}, limit)
    case Con{b, +t} 1n+p:
      limit_prefix(t, suf, p, limit)

law limit_suffix:
  for +pre: List<&2, U32>
  for +suf: List<&2, U32>
  for +n: Nat
  for limit: {Nat.is_le(B.length(B.concatenate(pre, suf)), n) == True{} : Bool}
  {Nat.is_le(B.length(suf), n) == True{} : Bool}
def limit_suffix(pre, suf, n, limit):
  match pre n:
    case Nil{} _:
      limit
    case Con{b, t} 0n:
      F.absurd_boolean({Nat.is_le(B.length(suf), 0n) == True{} : Bool}, limit)
    case Con{b, +t} 1n+p:
      N.increase_limit_right(B.length(suf), p, limit_suffix(t, suf, p, limit))

law suffix_after_prefix_positive:
  for +pre: List<&2, U32>
  for +suf: List<&2, U32>
  for +n: Nat
  for positive: BytesPositive(pre)
  for limit: {Nat.is_le(B.length(B.concatenate(pre, suf)), 1n+n) == True{} : Bool}
  {Nat.is_le(B.length(suf), n) == True{} : Bool}
def suffix_after_prefix_positive(pre, suf, n, positive, limit):
  match pre:
    case Nil{}:
      L.ex_false({Nat.is_le(B.length(suf), n) == True{} : Bool}, positive)
    case Con{b, +t}:
      limit_suffix(t, suf, n, limit)
