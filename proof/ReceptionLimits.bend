# Limits of every confirmed read; fabricates no events or POSIX result.
import Base
import ../contract/LAWS.bend as Laws
import ../contract/Interface.bend as I
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Data.bend as D
import ../contract/Bytes.bend as B
import ./Orders.bend as O
import ../contract/Logic.bend as L
import ./Foundations.bend as F

law reads_transitive:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a,b) == True{} : Bool}
  for bc: {Nat.is_le(b,c) == True{} : Bool}
  {Nat.is_le(a,c) == True{} : Bool}
def reads_transitive(a,b,c,ab,bc):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+k:
      {==}
    case 1n+x 0n _:
      F.absurd_boolean({Nat.is_le(1n+x,c) == True{} : Bool},ab)
    case 1n+x 1n+y 0n:
      F.absurd_boolean({False{} == True{} : Bool},bc)
    case 1n+x 1n+y 1n+z:
      reads_transitive(x,y,z,ab,bc)

law minimum_negative_exceeds_remaining:
  for +cap: Nat
  for +rest: Nat
  {Nat.is_le(Nat.min(cap,rest),rest) == True{} : Bool}
def minimum_negative_exceeds_remaining(cap,rest):
  match cap rest:
    case _ 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+c 1n+r:
      minimum_negative_exceeds_remaining(c,r)

law inside_of_remaining_negative_exceeds_declared:
  for +declared: Nat
  for +before: Nat
  for +count: Nat
  for existing: {Nat.is_le(before,declared) == True{} : Bool}
  for fits: {Nat.is_le(count,Nat.sub(declared,before)) == True{} : Bool}
  {Nat.is_le(Nat.add(before,count),declared) == True{} : Bool}
def inside_of_remaining_negative_exceeds_declared(declared,before,count,existing,fits):
  match declared before:
    case 0n 0n:
      fits
    case 0n 1n+p:
      F.absurd_boolean({Nat.is_le(Nat.add(1n+p,count),0n) == True{} : Bool},existing)
    case 1n+d 0n:
      fits
    case 1n+d 1n+a:
      inside_of_remaining_negative_exceeds_declared(d,a,count,existing,fits)

law consumption_confirmed_respects_declared_and_limit:
  for +declared: Nat
  for +before: Nat
  for +cap: Nat
  for +received: Nat
  for +limit: Nat
  for existing: {Nat.is_le(before,declared) == True{} : Bool}
  for real: {Nat.is_le(received,Nat.min(cap,Nat.sub(declared,before))) == True{} : Bool}
  for admitted: {Nat.is_le(declared,limit) == True{} : Bool}
  L.E<{Nat.is_le(Nat.add(before,received),declared) == True{} : Bool},
      {Nat.is_le(Nat.add(before,received),limit) == True{} : Bool}>
def consumption_confirmed_respects_declared_and_limit(declared,before,cap,received,limit,existing,real,admitted):
  +inside = inside_of_remaining_negative_exceeds_declared(declared,before,received,existing,
    reads_transitive(received,Nat.min(cap,Nat.sub(declared,before)),Nat.sub(declared,before),
      real,minimum_negative_exceeds_remaining(cap,Nat.sub(declared,before))))
  L.Both{inside,reads_transitive(Nat.add(before,received),declared,limit,inside,admitted)}

law header_measured_establishes_declaration_original:
  for +high: U32
  for +low: U32
  for +declared: Nat
  for measured: {B.nat64(declared) == Some{B.Number64{high,low}} : Maybe<&2,B.Number64>}
  {X.declared_equal(high,low,declared) == True{} : Bool}
def header_measured_establishes_declaration_original(high,low,declared,measured):
  %Equal.sym(Maybe<&2,B.Number64>,B.nat64(declared),Some{B.Number64{high,low}},measured) :
    {X.declared_equal_cases(high,low,_) == True{} : Bool}
  F.and_boolean_intro(U32.is_eq(high,high),U32.is_eq(low,low),
    Equal.cong(Cmp,Bool,c => Cmp.is_eq(c),U32.cmp(high,high),EQ{},O.u32_refl(high)),
    Equal.cong(Cmp,Bool,c => Cmp.is_eq(c),U32.cmp(low,low),EQ{},O.u32_refl(low)))

law consumption_real_bounded_establishes_rule2_original:
  for -a: I.Environment
  for -k: String
  for -t: Nat
  for -world: Nat
  for c: S.Configuration
  for -s: D.State
  for -input: X.Reception
  for +declared: Nat
  for +before: Nat
  for +cap: Nat
  for +received: Nat
  for declaration: Laws.LengthDeclared(input,declared)
  for existing: {Nat.is_le(before,declared) == True{} : Bool}
  for real: {Nat.is_le(received,Nat.min(cap,Nat.sub(declared,before))) == True{} : Bool}
  for admitted: {Nat.is_le(declared,R.limit_message(S.limits(c))) == True{} : Bool}
  Laws.Rule2(I.ReadBody{before,received,declared},a,k,I.Serve{world,c,s,input},t)
def consumption_real_bounded_establishes_rule2_original(a,k,t,world,c,s,input,declared,before,cap,received,declaration,existing,real,admitted):
  F.combined_pair(
    Laws.Rule2(I.ReadBody{before,received,declared},a,k,I.Serve{world,c,s,input},t),
    {Nat.is_le(Nat.add(before,received),declared) == True{} : Bool},
    {Nat.is_le(Nat.add(before,received),R.limit_message(S.limits(c))) == True{} : Bool},
    consumption_confirmed_respects_declared_and_limit(declared,before,cap,received,
      R.limit_message(S.limits(c)),existing,real,admitted),
    declared_fits => limit_fits => L.Both{declaration,L.Both{declared_fits,limit_fits}})
