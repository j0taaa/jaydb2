# Structural proof of every actual restoring-loop transition. The mathematical
# quotient keeps an explicit nonnegative carry coefficient until final bounds
# rule out every lost quotient bit.
import Base
import ./Int64DivisionNaturalStep.bend as N
import ./Int64RemainderStep.bend as Step
import ./Int64QuotientResidue.bend as Q
import ./Int64DivisionSource.bend as Source
import ./Int64BitInsert.bend as B
import ./Int64Proofs.bend as A
import ./Int64.bend as I
import ./Value.bend as V
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F

def quotient(result: I.Division) -> V.Int64:
  I.Division{q,r}=result
  q

def remainder(result: I.Division) -> V.Int64:
  I.Division{q,r}=result
  r

def total(d: V.Int64,+q: Nat,r: V.Int64) -> Nat:
  Nat.add(Nat.mul(A.unsigned(d),q),A.unsigned(r))

type Trace<-steps: Nat,-input: V.Int64,-d: V.Int64,-initial_q: Nat,-initial_r: V.Int64,-result: I.Division> is Type:
  Trace{natural_q: Nat,
    residue: Q.Residue<64n,A.unsigned(quotient(result)),natural_q>,
    arithmetic: {Source.actual_feed(steps,input,total(d,initial_q,initial_r)) == total(d,natural_q,remainder(result)) : Nat},
    small: {I.unsigned_lt(remainder(result),d) == True{} : Bool}}

law mathematical_prefix_step:
  for +bit: Bool
  for +subtract: Bool
  for +d: Nat
  for +q: Nat
  for +r: Nat
  for +next: Nat
  for +after: Nat
  for formed: {next == A.place(bit,r) : Nat}
  for difference: {next == Bool.pick(Nat,subtract,Nat.add(d,after),after) : Nat}
  {A.place(bit,Nat.add(Nat.mul(d,q),r)) == Nat.add(Nat.mul(d,A.place(subtract,q)),after) : Nat}
def mathematical_prefix_step(bit,subtract,d,q,r,next,after,formed,difference):
  Equal.trans(Nat,A.place(bit,Nat.add(Nat.mul(d,q),r)),Nat.add(Nat.mul(d,Nat.double(q)),A.place(bit,r)),Nat.add(Nat.mul(d,A.place(subtract,q)),after),N.binary_dividend_step(bit,d,q,r),
    Equal.trans(Nat,Nat.add(Nat.mul(d,Nat.double(q)),A.place(bit,r)),Nat.add(Nat.mul(d,Nat.double(q)),next),Nat.add(Nat.mul(d,A.place(subtract,q)),after),
      Equal.cong(Nat,Nat,v => Nat.add(Nat.mul(d,Nat.double(q)),v),A.place(bit,r),next,Equal.sym(Nat,next,A.place(bit,r),formed)),
      Equal.trans(Nat,Nat.add(Nat.mul(d,Nat.double(q)),next),Nat.add(Nat.mul(d,Nat.double(q)),Bool.pick(Nat,subtract,Nat.add(d,after),after)),Nat.add(Nat.mul(d,A.place(subtract,q)),after),
        Equal.cong(Nat,Nat,v => Nat.add(Nat.mul(d,Nat.double(q)),v),next,Bool.pick(Nat,subtract,Nat.add(d,after),after),difference),
        Equal.sym(Nat,Nat.add(Nat.mul(d,A.place(subtract,q)),after),Nat.add(Nat.mul(d,Nat.double(q)),Bool.pick(Nat,subtract,Nat.add(d,after),after)),N.quotient_bit_accounts_for_subtraction(subtract,d,q,after)))))

# The recursive output is arbitrary but carries its proved arithmetic facts.
def lift_trace(+steps: Nat,+input: V.Int64,+d: V.Int64,+initial_q: Nat,+initial_r: V.Int64,
  +next_q: Nat,+next_r: V.Int64,+result: I.Division,
  step: {A.place(I.negative(input),total(d,initial_q,initial_r)) == total(d,next_q,next_r) : Nat},
  trace: Trace<steps,I.shl(input),d,next_q,next_r,result>) -> Trace<1n+steps,input,d,initial_q,initial_r,result>:
  match trace:
    case Trace{+final_q,residue,arithmetic,small}:
      Trace{final_q,residue,Equal.trans(Nat,Source.actual_feed(1n+steps,input,total(d,initial_q,initial_r)),Source.actual_feed(steps,I.shl(input),total(d,next_q,next_r)),total(d,final_q,remainder(result)),
        Equal.cong(Nat,Nat,prefix => Source.actual_feed(steps,I.shl(input),prefix),A.place(I.negative(input),total(d,initial_q,initial_r)),total(d,next_q,next_r),step),arithmetic),small}

# All loop invariant premises are mathematical initial-state facts. The public
# unsigned theorem derives them for q=r=0 and the actual nonzero divisor.
law actual_restoring_loop_trace:
  for +steps: Nat
  for +input: V.Int64
  for +d: V.Int64
  for +q: V.Int64
  for +r: V.Int64
  for +natural_q: Nat
  for residue: Q.Residue<64n,A.unsigned(q),natural_q>
  for small: {I.unsigned_lt(r,d) == True{} : Bool}
  for +bound: {Cmp.is_le(Word.cmp(64n,A.bits(d),A.sign_threshold(63n))) == True{} : Bool}
  Trace<steps,input,d,natural_q,r,I.divide_step(steps,input,d,q,r)>
def actual_restoring_loop_trace(steps,input,d,q,r,natural_q,residue,small,bound):
  match steps:
    case 0n: Trace{natural_q,residue,{==},small}
    case 1n+p:
      F.combined_pair(Trace<1n+p,input,d,natural_q,r,I.divide_step(1n+p,input,d,q,r)>,
        {A.unsigned(B.insert(r,I.negative(input))) == A.place(I.negative(input),A.unsigned(r)) : Nat},
        L.E<{A.unsigned(B.insert(r,I.negative(input))) == Bool.pick(Nat,Step.decision(B.insert(r,I.negative(input)),d),Nat.add(A.unsigned(d),A.unsigned(Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d))),A.unsigned(Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d))) : Nat},
          {I.unsigned_lt(Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d),d) == True{} : Bool}>,
        Step.actual_remainder_step(r,input,d,small,bound),
        formed => rest =>
          F.combined_pair(Trace<1n+p,input,d,natural_q,r,I.divide_step(1n+p,input,d,q,r)>,
            {A.unsigned(B.insert(r,I.negative(input))) == Bool.pick(Nat,Step.decision(B.insert(r,I.negative(input)),d),Nat.add(A.unsigned(d),A.unsigned(Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d))),A.unsigned(Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d))) : Nat},
            {I.unsigned_lt(Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d),d) == True{} : Bool},rest,
            difference => next_small =>
              lift_trace(p,input,d,natural_q,r,A.place(Step.decision(B.insert(r,I.negative(input)),d),natural_q),Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d),
                I.divide_step(p,I.shl(input),d,B.insert(q,Step.decision(B.insert(r,I.negative(input)),d)),Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d)),
                mathematical_prefix_step(I.negative(input),Step.decision(B.insert(r,I.negative(input)),d),A.unsigned(d),natural_q,A.unsigned(r),A.unsigned(B.insert(r,I.negative(input))),A.unsigned(Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d)),formed,difference),
                actual_restoring_loop_trace(p,I.shl(input),d,B.insert(q,Step.decision(B.insert(r,I.negative(input)),d)),Step.after_subtract(Step.decision(B.insert(r,I.negative(input)),d),B.insert(r,I.negative(input)),d),A.place(Step.decision(B.insert(r,I.negative(input)),d),natural_q),
                  Q.actual_quotient_bit_preserves_residue(q,natural_q,Step.decision(B.insert(r,I.negative(input)),d),residue),next_small,bound))))
