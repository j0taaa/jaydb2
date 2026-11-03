import Base
import ../../contract/LAWS.bend as Laws
import ../../contract/Interface.bend as I
import ../../contract/Resources.bend as X
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../contract/Data.bend as D
import ../../contract/Bytes.bend as B
import ../../proof/ReceptionLimits.bend as Q

# Does not receive ReadBounded as a premise: constructs it from the actual syscall
# consumption bound, header admission and exact representation.
law read_confirmed_satisfies_rule_original_for_any_body:
  for -a: I.Environment
  for -k: String
  for -t: Nat
  for -world: Nat
  for c: S.Configuration
  for -s: D.State
  for +high: U32
  for +low: U32
  for -body: List<&2,U32>
  for +declared: Nat
  for +before: Nat
  for +cap: Nat
  for +received: Nat
  for measure_header: {B.nat64(declared) == Some{B.Number64{high,low}} : Maybe<&2,B.Number64>}
  for existing: {Nat.is_le(before,declared) == True{} : Bool}
  for real: {Nat.is_le(received,Nat.min(cap,Nat.sub(declared,before))) == True{} : Bool}
  for admitted: {Nat.is_le(declared,R.limit_message(S.limits(c))) == True{} : Bool}
  Laws.Rule2(I.ReadBody{before,received,declared},a,k,
    I.Serve{world,c,s,X.BodyReceived{high,low,body}},t)
def read_confirmed_satisfies_rule_original_for_any_body(a,k,t,world,c,s,high,low,body,declared,before,cap,received,measure_header,existing,real,admitted):
  Q.consumption_real_bounded_establishes_rule2_original(a,k,t,world,c,s,
    X.BodyReceived{high,low,body},declared,before,cap,received,
    Q.header_measured_establishes_declaration_original(high,low,declared,measure_header),
    existing,real,admitted)
