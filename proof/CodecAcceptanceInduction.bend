# Phase types for ONE lexicographic recursion. Length is only
# mathematical; it is not an additional quota supplied to the decoder.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./CodecTrace.bend as R
import ./CodecAcceptanceChildren.bend as H
import ./CodecAcceptancePrefix.bend as X
import ./CodecLimitsSequences.bend as S
import ./CodecAcceptanceRecord.bend as G

def Obligation(n: Nat, phase: Nat, xs: List<&2, S.ValueSegmented>, ys: List<&2, S.FieldSegmented>,
  +bs: List<&2, U32>, body: B.Number64, ceiling: B.Number64, v: D.Value) -> Type:
  match phase:
    case 0n:
      L.E<{Nat.is_le(B.length(bs), n) == True{} : Bool},
        L.E<{B.octets_all_valid(bs) == True{} : Bool},
          {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}>>
    case 1n:
      L.E<H.ChildrenRead(xs, n), {B.octets_all_valid(S.bytes_values(xs)) == True{} : Bool}>
    case 2n:
      L.E<G.FieldsRead(ys, n), {B.octets_all_valid(S.bytes_fields(ys)) == True{} : Bool}>
    case 3n+p:
      Unit

def Conclusion(phase: Nat, xs: List<&2, S.ValueSegmented>, ys: List<&2, S.FieldSegmented>,
  bs: List<&2, U32>, v: D.Value) -> Type:
  match phase:
    case 0n:
      P.Encoding(v, bs)
    case 1n:
      S.ValuesCanonical(xs)
    case 2n:
      S.FieldsCanonical(ys)
    case 3n+p:
      Unit
