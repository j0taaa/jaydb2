# Complete correctness of the actual bounded shift-and-add algorithm.
# A rejected total is proved unequal to every unsigned 64-bit value.
import Base
import ./Int64UnsignedStep.bend as S
import ./Int64MultiplierFuel.bend as Fuel
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A

def UnsignedResult(+value: Nat,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{r}: {A.unsigned(r) == value : Nat}
    case None{}: @r: V.Int64 -> {A.unsigned(r) == value : Nat} -> Empty

def overflow(+a: V.Int64,+b: V.Int64,+accumulator: V.Int64) -> Bool:
  (I.odd(b) && I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator)) || (I.negative(a) && Bool.not(I.zero(I.shr(b))))

def continue_correct(+n: Nat,+a: V.Int64,+b: V.Int64,+accumulator: V.Int64,+over: Bool,
  evidence: Bool.pick(Type,over,S.Beyond<64n,S.total(a,b,accumulator)>,{S.total(a,b,accumulator) == S.next_total(I.odd(b),a,b,accumulator) : Nat}),
  recursive: UnsignedResult(S.next_total(I.odd(b),a,b,accumulator),I.multiply_step(n,I.shl(a),I.shr(b),S.selected_word(I.odd(b),a,accumulator)))) ->
  UnsignedResult(S.total(a,b,accumulator),I.continue_unsigned(over,u => I.multiply_step(n,I.shl(a),I.shr(b),S.selected_word(I.odd(b),a,accumulator)))):
  match over:
    case True{}:
      r => same => S.excess_excludes_every_word(S.total(a,b,accumulator),r,evidence,same)
    case False{}:
      %Equal.sym(Nat,S.total(a,b,accumulator),S.next_total(I.odd(b),a,b,accumulator),evidence) :
        UnsignedResult(_,I.multiply_step(n,I.shl(a),I.shr(b),S.selected_word(I.odd(b),a,accumulator)))
      recursive

law unsigned_multiply_step_is_exact:
  for +n: Nat
  for +a: V.Int64
  for +b: V.Int64
  for +accumulator: V.Int64
  for covered: {Fuel.shrink(n,b) == V.Int64{0,0} : V.Int64}
  UnsignedResult(S.total(a,b,accumulator),I.multiply_step(n,a,b,accumulator))
def unsigned_multiply_step_is_exact(n,a,b,accumulator,covered):
  match n:
    case 0n:
      %Equal.sym(V.Int64,b,V.Int64{0,0},covered) : {A.unsigned(accumulator) == S.total(a,_,accumulator) : Nat}
      Equal.sym(Nat,Nat.add(A.unsigned(accumulator),0n),A.unsigned(accumulator),A.add_zero_right(A.unsigned(accumulator)))
    case 1n+p:
      continue_correct(p,a,b,accumulator,overflow(a,b,accumulator),S.actual_step_evidence(a,b,accumulator),
        unsigned_multiply_step_is_exact(p,I.shl(a),I.shr(b),S.selected_word(I.odd(b),a,accumulator),covered))

# This public theorem derives fuel adequacy; it has no invariant premises.
law unsigned_multiply_is_natural_product:
  for +a: V.Int64
  for +b: V.Int64
  UnsignedResult(Nat.mul(A.unsigned(b),A.unsigned(a)),I.multiply_step(64n,a,b,V.Int64{0,0}))
def unsigned_multiply_is_natural_product(a,b):
  unsigned_multiply_step_is_exact(64n,a,b,V.Int64{0,0},Fuel.sixty_four_steps_cover_every_multiplier(b))
