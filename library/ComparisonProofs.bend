# Optional comparison proofs for the actual Value and Int64 comparators.
# Kept separate from runtime helpers so their imports remain unchanged.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Value.bend as V
import ./StructuralEqualityProofs.bend as Structural
import ./Int64.bend as I
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

# General correctness of the actual structural comparator. No validity premise:
# malformed list/record tails are compared as structure too.

# Bridge the actual primitive Bool/U32 comparators to propositional equality.
def bool_equal_refl(b: Bool) -> {Bool.not(Bool.xor(b, b)) == True{} : Bool}:
  Structural.bool_equal_refl(b)

def bool_equal_sound(a: Bool, b: Bool,
  h: {Bool.not(Bool.xor(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  Structural.bool_equal_sound(a, b, h)

def u32_equal_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  Structural.u32_equal_refl(a)

def u32_equal_sound(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  Structural.u32_equal_sound(a, b, h)

law equal_reflexive:
  for +v: D.Value
  {V.equal(v, v) == True{} : Bool}
def equal_reflexive(v):
  Structural.equal_reflexive(v)

law equal_sound:
  for +a: D.Value
  for +b: D.Value
  for +h: {V.equal(a, b) == True{} : Bool}
  {a == b : D.Value}
def equal_sound(a, b, h):
  Structural.equal_sound(a, b, h)

law equal_complete:
  for +a: D.Value
  for +b: D.Value
  for h: {a == b : D.Value}
  {V.equal(a, b) == True{} : Bool}
def equal_complete(a, b, h):
  Structural.equal_complete(a, b, h)

law equal_true_inverse:
  for +a: D.Value
  for +b: D.Value
  for h: {V.equal(a, b) == True{} : Bool}
  {V.equal(b, a) == True{} : Bool}
def equal_true_inverse(a, b, h):
  Structural.equal_true_inverse(a, b, h)

# A false comparison proves structural inequality, rather than merely being
# evidence about an implementation-specific predicate.
law unequal_values_differ:
  for +a: D.Value
  for +b: D.Value
  for h: {V.equal(a, b) == False{} : Bool}
  {a == b : D.Value} -> Empty
def unequal_values_differ(a, b, h):
  Structural.unequal_values_differ(a, b, h)

# Strict-order properties of the actual signed64 comparator, not an assumed
# integer specification.

# Equality of bit comparisons survives a common XOR mask.
def eq_fin(a: Bool, b: Bool, c: Cmp) ->
  {Cmp.is_eq(Word.cmp.fin(a,b,c)) == Cmp.is_eq(c) && Cmp.is_eq(Bool.cmp(a,b)) : Bool}:
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def eq_bool_xor(a: Bool, b: Bool, m: Bool) ->
  {Cmp.is_eq(Bool.cmp(Bool.xor(a,m),Bool.xor(b,m))) == Cmp.is_eq(Bool.cmp(a,b)) : Bool}:
  match a b m:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: {==}
    case True{} False{} True{}: {==}
    case True{} True{} False{}: {==}
    case True{} True{} True{}: {==}

def and_cong(+a: Bool, +b: Bool, +c: Bool, +d: Bool,
  ab: {a == b : Bool}, cd: {c == d : Bool}) -> {a && c == b && d : Bool}:
  Equal.trans(Bool,a && c,b && c,b && d,
    Equal.cong(Bool,Bool,x => x && c,a,b,ab),
    Equal.cong(Bool,Bool,x => b && x,c,d,cd))

law eq_word_xor:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +m: Word(n)
  {Cmp.is_eq(Word.cmp(n,Word.xor(n,a,m),Word.xor(n,b,m))) == Cmp.is_eq(Word.cmp(n,a,b)) : Bool}
def eq_word_xor(n,a,b,m):
  match n:
    case Zero{}: {==}
    case Succ{p}:
      match a b m:
        case WCon{+x,+at} WCon{+y,+bt} WCon{+z,+mt}:
          Equal.trans(Bool,
            Cmp.is_eq(Word.cmp.fin(Bool.xor(x,z),Bool.xor(y,z),Word.cmp(p,Word.xor(p,at,mt),Word.xor(p,bt,mt)))),
            Cmp.is_eq(Word.cmp(p,Word.xor(p,at,mt),Word.xor(p,bt,mt))) && Cmp.is_eq(Bool.cmp(Bool.xor(x,z),Bool.xor(y,z))),
            Cmp.is_eq(Word.cmp.fin(x,y,Word.cmp(p,at,bt))),
            eq_fin(Bool.xor(x,z),Bool.xor(y,z),Word.cmp(p,Word.xor(p,at,mt),Word.xor(p,bt,mt))),
            Equal.trans(Bool,
              Cmp.is_eq(Word.cmp(p,Word.xor(p,at,mt),Word.xor(p,bt,mt))) && Cmp.is_eq(Bool.cmp(Bool.xor(x,z),Bool.xor(y,z))),
              Cmp.is_eq(Word.cmp(p,at,bt)) && Cmp.is_eq(Bool.cmp(x,y)),
              Cmp.is_eq(Word.cmp.fin(x,y,Word.cmp(p,at,bt))),
              and_cong(Cmp.is_eq(Word.cmp(p,Word.xor(p,at,mt),Word.xor(p,bt,mt))),Cmp.is_eq(Word.cmp(p,at,bt)),
                Cmp.is_eq(Bool.cmp(Bool.xor(x,z),Bool.xor(y,z))),Cmp.is_eq(Bool.cmp(x,y)),
                eq_word_xor(p,at,bt,mt),eq_bool_xor(x,y,z)),
              Equal.sym(Bool,Cmp.is_eq(Word.cmp.fin(x,y,Word.cmp(p,at,bt))),
                Cmp.is_eq(Word.cmp(p,at,bt)) && Cmp.is_eq(Bool.cmp(x,y)),eq_fin(x,y,Word.cmp(p,at,bt)))))

law eq_u32_xor:
  for +a: U32
  for +b: U32
  for +m: U32
  {U32.is_eq(U32.xor(a,m),U32.xor(b,m)) == U32.is_eq(a,b) : Bool}
def eq_u32_xor(a,b,m):
  match a b m:
    case U32{x} U32{y} U32{z}: eq_word_xor(32n,x,y,z)

def priority_lt(c: Cmp, d: Cmp) ->
  {Cmp.is_lt(O.priority(c,d)) == Cmp.is_lt(c) || (Cmp.is_eq(c) && Cmp.is_lt(d)) : Bool}:
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

# Lexicographic comparison of the sign-bit-flipped high word and low word.
# This is a rank order, independently equipped with comparison coherence.
def rank_order(a: V.Int64,b: V.Int64) -> Cmp:
  match a b:
    case V.Int64{h,l} V.Int64{i,j}:
      O.priority(U32.cmp(U32.xor(h,2147483648),U32.xor(i,2147483648)),U32.cmp(l,j))

law rank_matches_lt:
  for +a: V.Int64
  for +b: V.Int64
  {Cmp.is_lt(rank_order(a,b)) == I.lt(a,b) : Bool}
def rank_matches_lt(a,b):
  match a b:
    case V.Int64{+h,+l} V.Int64{+i,+j}:
      Equal.trans(Bool,
        Cmp.is_lt(O.priority(U32.cmp(U32.xor(h,2147483648),U32.xor(i,2147483648)),U32.cmp(l,j))),
        U32.is_lt(U32.xor(h,2147483648),U32.xor(i,2147483648)) ||
          (U32.is_eq(U32.xor(h,2147483648),U32.xor(i,2147483648)) && U32.is_lt(l,j)),
        I.lt(V.Int64{h,l},V.Int64{i,j}),
        priority_lt(U32.cmp(U32.xor(h,2147483648),U32.xor(i,2147483648)),U32.cmp(l,j)),
        Equal.cong(Bool,Bool,e => U32.is_lt(U32.xor(h,2147483648),U32.xor(i,2147483648)) || (e && U32.is_lt(l,j)),
          U32.is_eq(U32.xor(h,2147483648),U32.xor(i,2147483648)),U32.is_eq(h,i),eq_u32_xor(h,i,2147483648)))

law rank_coherent:
  for +a: V.Int64
  for +b: V.Int64
  for +c: V.Int64
  O.Coherent(rank_order(a,b),rank_order(b,c),rank_order(a,c))
def rank_coherent(a,b,c):
  match a b c:
    case V.Int64{+h,+l} V.Int64{+i,+j} V.Int64{+k,+m}:
      O.compose_orders(U32.cmp(U32.xor(h,2147483648),U32.xor(i,2147483648)),
        U32.cmp(U32.xor(i,2147483648),U32.xor(k,2147483648)),
        U32.cmp(U32.xor(h,2147483648),U32.xor(k,2147483648)),
        U32.cmp(l,j),U32.cmp(j,m),U32.cmp(l,m),
        O.u32_coherent(U32.xor(h,2147483648),U32.xor(i,2147483648),U32.xor(k,2147483648)),
        O.u32_coherent(l,j,m))

law rank_reflexive:
  for +a: V.Int64
  {rank_order(a,a) == EQ{} : Cmp}
def rank_reflexive(a):
  match a:
    case V.Int64{+h,+l}:
      %Equal.sym(Cmp,U32.cmp(U32.xor(h,2147483648),U32.xor(h,2147483648)),EQ{},O.u32_refl(U32.xor(h,2147483648))) : {O.priority(_,U32.cmp(l,l)) == EQ{} : Cmp}
      O.u32_refl(l)

law lt_irreflexive:
  for +a: V.Int64
  {I.lt(a,a) == False{} : Bool}
def lt_irreflexive(a):
  Equal.trans(Bool,I.lt(a,a),Cmp.is_lt(rank_order(a,a)),False{},
    Equal.sym(Bool,Cmp.is_lt(rank_order(a,a)),I.lt(a,a),rank_matches_lt(a,a)),
    Equal.cong(Cmp,Bool,c => Cmp.is_lt(c),rank_order(a,a),EQ{},rank_reflexive(a)))

law lt_transitive:
  for +a: V.Int64
  for +b: V.Int64
  for +c: V.Int64
  for ab: {I.lt(a,b) == True{} : Bool}
  for bc: {I.lt(b,c) == True{} : Bool}
  {I.lt(a,c) == True{} : Bool}
def lt_transitive(a,b,c,ab,bc):
  ab_rank = Equal.trans(Bool,Cmp.is_lt(rank_order(a,b)),I.lt(a,b),True{},rank_matches_lt(a,b),ab)
  bc_rank = Equal.trans(Bool,Cmp.is_lt(rank_order(b,c)),I.lt(b,c),True{},rank_matches_lt(b,c),bc)
  h1 = {(%O.cmp_lt(rank_order(a,b),ab_rank) : O.Coherent(_,rank_order(b,c),rank_order(a,c))
    rank_coherent(a,b,c)) : O.Coherent(LT{},rank_order(b,c),rank_order(a,c))}
  h2 = {(%O.cmp_lt(rank_order(b,c),bc_rank) : O.Coherent(LT{},_,rank_order(a,c))
    h1) : O.Coherent(LT{},LT{},rank_order(a,c))}
  Equal.trans(Bool,I.lt(a,c),Cmp.is_lt(rank_order(a,c)),True{},
    Equal.sym(Bool,Cmp.is_lt(rank_order(a,c)),I.lt(a,c),rank_matches_lt(a,c)),
    Equal.cong(Cmp,Bool,x => Cmp.is_lt(x),rank_order(a,c),LT{},h2))

def asymmetry_choice(+a: V.Int64,+b: V.Int64,flag: Bool,
  ab: {I.lt(a,b) == True{} : Bool},ba: {I.lt(b,a) == flag : Bool}) -> {flag == False{} : Bool}:
  match flag:
    case False{}: {==}
    case True{}:
      F.absurd_boolean({True{} == False{} : Bool},
        Equal.trans(Bool,False{},I.lt(a,a),True{},
          Equal.sym(Bool,I.lt(a,a),False{},lt_irreflexive(a)),lt_transitive(a,b,a,ab,ba)))

law lt_asymmetric:
  for +a: V.Int64
  for +b: V.Int64
  for ab: {I.lt(a,b) == True{} : Bool}
  {I.lt(b,a) == False{} : Bool}
def lt_asymmetric(a,b,ab):
  asymmetry_choice(a,b,I.lt(b,a),ab,{==})

# Optional total-order extension for the actual Int64 comparator; no arithmetic model.

def unmask_equal(+a: U32,+b: U32,
  e: {U32.cmp(U32.xor(a,2147483648),U32.xor(b,2147483648)) == EQ{} : Cmp}) -> {a == b : U32}:
  O.u32_equal(a,b,O.cmp_eq(U32.cmp(a,b),
    Equal.trans(Bool,U32.is_eq(a,b),U32.is_eq(U32.xor(a,2147483648),U32.xor(b,2147483648)),True{},
      Equal.sym(Bool,U32.is_eq(U32.xor(a,2147483648),U32.xor(b,2147483648)),U32.is_eq(a,b),eq_u32_xor(a,b,2147483648)),
      Equal.cong(Cmp,Bool,c => Cmp.is_eq(c),U32.cmp(U32.xor(a,2147483648),U32.xor(b,2147483648)),EQ{},e))))

law rank_equal:
  for +a: V.Int64
  for +b: V.Int64
  for e: {rank_order(a,b) == EQ{} : Cmp}
  {a == b : V.Int64}
def rank_equal(a,b,e):
  match a b:
    case V.Int64{+h,+l} V.Int64{+i,+j}:
      F.combined_pair({V.Int64{h,l} == V.Int64{i,j} : V.Int64},
        {U32.cmp(U32.xor(h,2147483648),U32.xor(i,2147483648)) == EQ{} : Cmp},
        {U32.cmp(l,j) == EQ{} : Cmp},
        O.priority_equal(U32.cmp(U32.xor(h,2147483648),U32.xor(i,2147483648)),U32.cmp(l,j),e),
        high => low =>
          %unmask_equal(h,i,high) : {V.Int64{h,l} == V.Int64{_,j} : V.Int64}
          Equal.cong(U32,V.Int64,x => V.Int64{h,x},l,j,O.u32_equal(l,j,low)))

def reverse_cmp(c: Cmp) -> Cmp:
  match c:
    case LT{}: GT{}
    case EQ{}: EQ{}
    case GT{}: LT{}

def coherent_inverse(c: Cmp,d: Cmp,h: O.Coherent(c,d,EQ{})) -> {d == reverse_cmp(c) : Cmp}:
  match c d:
    case EQ{} EQ{}: {==}
    case EQ{} LT{}: Equal.sym(Cmp,EQ{},LT{},h)
    case EQ{} GT{}: Equal.sym(Cmp,EQ{},GT{},h)
    case LT{} GT{}: {==}
    case GT{} LT{}: {==}
    case LT{} LT{}:
      F.absurd_boolean({LT{} == GT{} : Cmp},Equal.cong(Cmp,Bool,x => Cmp.is_lt(x),EQ{},LT{},h))
    case LT{} EQ{}:
      F.absurd_boolean({EQ{} == GT{} : Cmp},Equal.cong(Cmp,Bool,x => Cmp.is_lt(x),EQ{},LT{},h))
    case GT{} GT{}:
      F.absurd_boolean({GT{} == LT{} : Cmp},Equal.cong(Cmp,Bool,x => Cmp.is_gt(x),EQ{},GT{},h))
    case GT{} EQ{}:
      F.absurd_boolean({EQ{} == LT{} : Cmp},Equal.cong(Cmp,Bool,x => Cmp.is_gt(x),EQ{},GT{},h))

law rank_reverse:
  for +a: V.Int64
  for +b: V.Int64
  {rank_order(b,a) == reverse_cmp(rank_order(a,b)) : Cmp}
def rank_reverse(a,b):
  coherent_inverse(rank_order(a,b),rank_order(b,a),
    (%rank_reflexive(a) : O.Coherent(rank_order(a,b),rank_order(b,a),_)
      rank_coherent(a,b,a)))

# A classification of the rank result by the library's actual strict relation.
# Strictness and mutual exclusivity are supplied by lt_irreflexive/asymmetric.
def Classification(a: V.Int64,b: V.Int64,c: Cmp) -> Type:
  match c:
    case LT{}: {I.lt(a,b) == True{} : Bool}
    case EQ{}: {a == b : V.Int64}
    case GT{}: {I.lt(b,a) == True{} : Bool}

def classify_case(+a: V.Int64,+b: V.Int64,c: Cmp,e: {rank_order(a,b) == c : Cmp}) -> Classification(a,b,c):
  match c:
    case LT{}:
      Equal.trans(Bool,I.lt(a,b),Cmp.is_lt(rank_order(a,b)),True{},
        Equal.sym(Bool,Cmp.is_lt(rank_order(a,b)),I.lt(a,b),rank_matches_lt(a,b)),
        Equal.cong(Cmp,Bool,x => Cmp.is_lt(x),rank_order(a,b),LT{},e))
    case EQ{}: rank_equal(a,b,e)
    case GT{}:
      Equal.trans(Bool,I.lt(b,a),Cmp.is_lt(rank_order(b,a)),True{},
        Equal.sym(Bool,Cmp.is_lt(rank_order(b,a)),I.lt(b,a),rank_matches_lt(b,a)),
        Equal.cong(Cmp,Bool,x => Cmp.is_lt(x),rank_order(b,a),LT{},
          Equal.trans(Cmp,rank_order(b,a),reverse_cmp(rank_order(a,b)),LT{},rank_reverse(a,b),
            Equal.cong(Cmp,Cmp,x => reverse_cmp(x),rank_order(a,b),GT{},e))))

law rank_classification:
  for +a: V.Int64
  for +b: V.Int64
  Classification(a,b,rank_order(a,b))
def rank_classification(a,b):
  classify_case(a,b,rank_order(a,b),{==})

def Trichotomy(+a: V.Int64,+b: V.Int64) -> Type:
  L.Disjunction<{I.lt(a,b) == True{} : Bool},L.Disjunction<{a == b : V.Int64},{I.lt(b,a) == True{} : Bool}>>

def classify_sum(a: V.Int64,b: V.Int64,c: Cmp,h: Classification(a,b,c)) -> Trichotomy(a,b):
  match c:
    case LT{}: L.Left{h}
    case EQ{}: L.Right{L.Left{h}}
    case GT{}: L.Right{L.Right{h}}

law lt_trichotomy:
  for +a: V.Int64
  for +b: V.Int64
  Trichotomy(a,b)
def lt_trichotomy(a,b):
  classify_sum(a,b,rank_order(a,b),rank_classification(a,b))
