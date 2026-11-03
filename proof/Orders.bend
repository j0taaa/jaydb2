# General algebra of actual Base comparisons, used for the registry.
import Base
import ../contract/Logic.bend as L
import ./Foundations.bend as F

def priority(first: Cmp, second: Cmp) -> Cmp:
  match first:
    case EQ{}:
      second
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# Transitivity and substitution of equals within one proposition.
def Coherent(ab: Cmp, bc: Cmp, ac: Cmp) -> Type:
  match ab bc:
    case EQ{} _:
      {ac == bc : Cmp}
    case _ EQ{}:
      {ac == ab : Cmp}
    case LT{} LT{}:
      {ac == LT{} : Cmp}
    case GT{} GT{}:
      {ac == GT{} : Cmp}
    case _ _:
      Unit

def left_lt(c: Cmp) -> Coherent(c, LT{}, LT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      Unit{}

def left_gt(c: Cmp) -> Coherent(c, GT{}, GT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Unit{}
    case GT{}:
      {==}

def right_lt(c: Cmp) -> Coherent(LT{}, c, LT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      Unit{}

def right_gt(c: Cmp) -> Coherent(GT{}, c, GT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Unit{}
    case GT{}:
      {==}

law compose_orders:
  for ab: Cmp
  for bc: Cmp
  for -ac: Cmp
  for xy: Cmp
  for yz: Cmp
  for -xz: Cmp
  for h: Coherent(ab, bc, ac)
  for t: Coherent(xy, yz, xz)
  Coherent(priority(ab, xy), priority(bc, yz), priority(ac, xz))
def compose_orders(ab, bc, ac, xy, yz, xz, h, t):
  match ab bc:
    case EQ{} EQ{}:
      %Equal.sym(Cmp, ac, EQ{}, h) : Coherent(xy, yz, priority(_, xz))
      t
    case EQ{} LT{}:
      %Equal.sym(Cmp, ac, LT{}, h) : Coherent(xy, LT{}, priority(_, xz))
      left_lt(xy)
    case EQ{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : Coherent(xy, GT{}, priority(_, xz))
      left_gt(xy)
    case LT{} EQ{}:
      %Equal.sym(Cmp, ac, LT{}, h) : Coherent(LT{}, yz, priority(_, xz))
      right_lt(yz)
    case GT{} EQ{}:
      %Equal.sym(Cmp, ac, GT{}, h) : Coherent(GT{}, yz, priority(_, xz))
      right_gt(yz)
    case LT{} LT{}:
      %Equal.sym(Cmp, ac, LT{}, h) : Coherent(LT{}, LT{}, priority(_, xz))
      {==}
    case GT{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : Coherent(GT{}, GT{}, priority(_, xz))
      {==}
    case LT{} GT{}:
      Unit{}
    case GT{} LT{}:
      Unit{}

law bool_coherent:
  for a: Bool
  for b: Bool
  for c: Bool
  Coherent(Bool.cmp(a, b), Bool.cmp(b, c), Bool.cmp(a, c))
def bool_coherent(a, b, c):
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      Unit{}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      Unit{}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

law word_fin_priority:
  for a: Bool
  for b: Bool
  for c: Cmp
  {Word.cmp.fin(a, b, c) == priority(c, Bool.cmp(a, b)) : Cmp}
def word_fin_priority(a, b, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law word_coherent:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  Coherent(Word.cmp(n, a, b), Word.cmp(n, b, c), Word.cmp(n, a, c))
def word_coherent(n, a, b, c):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b c:
        case WCon{ah, at} WCon{bh, bt} WCon{ch, ct}:
          %Equal.sym(Cmp, Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)),
            priority(Word.cmp(p, at, bt), Bool.cmp(ah, bh)),
            word_fin_priority(ah, bh, Word.cmp(p, at, bt))) : Coherent(_, Word.cmp(1n+p, WCon{bh, bt}, WCon{ch, ct}), Word.cmp(1n+p, WCon{ah, at}, WCon{ch, ct}))
          %Equal.sym(Cmp, Word.cmp.fin(bh, ch, Word.cmp(p, bt, ct)),
            priority(Word.cmp(p, bt, ct), Bool.cmp(bh, ch)),
            word_fin_priority(bh, ch, Word.cmp(p, bt, ct))) : Coherent(priority(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), _, Word.cmp(1n+p, WCon{ah, at}, WCon{ch, ct}))
          %Equal.sym(Cmp, Word.cmp.fin(ah, ch, Word.cmp(p, at, ct)),
            priority(Word.cmp(p, at, ct), Bool.cmp(ah, ch)),
            word_fin_priority(ah, ch, Word.cmp(p, at, ct))) : Coherent(priority(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), priority(Word.cmp(p, bt, ct), Bool.cmp(bh, ch)), _)
          compose_orders(Word.cmp(p, at, bt), Word.cmp(p, bt, ct), Word.cmp(p, at, ct),
            Bool.cmp(ah, bh), Bool.cmp(bh, ch), Bool.cmp(ah, ch),
            word_coherent(p, at, bt, ct), bool_coherent(ah, bh, ch))

law bool_refl:
  for b: Bool
  {Bool.cmp(b, b) == EQ{} : Cmp}
def bool_refl(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law word_refl:
  for +n: Nat
  for +w: Word(n)
  {Word.cmp(n, w, w) == EQ{} : Cmp}
def word_refl(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{h, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_refl(p, t)) : {Word.cmp.fin(h, h, _) == EQ{} : Cmp}
          bool_refl(h)

law u32_coherent:
  for a: U32
  for b: U32
  for c: U32
  Coherent(U32.cmp(a, b), U32.cmp(b, c), U32.cmp(a, c))
def u32_coherent(a, b, c):
  match a b c:
    case U32{x} U32{y} U32{z}:
      word_coherent(32n, x, y, z)

law u32_refl:
  for a: U32
  {U32.cmp(a, a) == EQ{} : Cmp}
def u32_refl(a):
  match a:
    case U32{x}:
      word_refl(32n, x)

law string_go_priority:
  for a: String
  for b: String
  for c: Cmp
  {String.order.go(a, b, c) == priority(c, String.order(a, b)) : Cmp}
def string_go_priority(a, b, c):
  match a b c:
    case SNil{} SNil{} EQ{}:
      {==}
    case SNil{} SCon{Chr{x}, t} EQ{}:
      {==}
    case SCon{Chr{x}, t} SNil{} EQ{}:
      {==}
    case SCon{Chr{x}, t} SCon{Chr{y}, u} EQ{}:
      {==}
    case SNil{} SNil{} LT{}:
      {==}
    case SNil{} SCon{Chr{x}, t} LT{}:
      {==}
    case SCon{Chr{x}, t} SNil{} LT{}:
      {==}
    case SCon{Chr{x}, t} SCon{Chr{y}, u} LT{}:
      {==}
    case SNil{} SNil{} GT{}:
      {==}
    case SNil{} SCon{Chr{x}, t} GT{}:
      {==}
    case SCon{Chr{x}, t} SNil{} GT{}:
      {==}
    case SCon{Chr{x}, t} SCon{Chr{y}, u} GT{}:
      {==}

law string_cons:
  for x: U32
  for y: U32
  for a: String
  for b: String
  {String.order(SCon{Chr{x}, a}, SCon{Chr{y}, b}) ==
    priority(U32.cmp(x, y), String.order(a, b)) : Cmp}
def string_cons(x, y, a, b):
  string_go_priority(a, b, U32.cmp(x, y))

law string_coherent:
  for +a: String
  for +b: String
  for +c: String
  Coherent(String.order(a, b), String.order(b, c), String.order(a, c))
def string_coherent(a, b, c):
  match a b c:
    case SNil{} SNil{} SNil{}:
      {==}
    case SNil{} SNil{} SCon{Chr{x}, t}:
      {==}
    case SNil{} SCon{Chr{x}, t} SNil{}:
      Unit{}
    case SCon{Chr{x}, t} SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{x}, t} SCon{Chr{y}, u}:
      right_lt(String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}))
    case SCon{Chr{x}, t} SNil{} SCon{Chr{y}, u}:
      Unit{}
    case SCon{Chr{x}, t} SCon{Chr{y}, u} SNil{}:
      left_gt(String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}))
    case SCon{Chr{x}, t} SCon{Chr{y}, u} SCon{Chr{z}, v}:
      %Equal.sym(Cmp, String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}), priority(U32.cmp(x, y), String.order(t, u)), string_cons(x, y, t, u)) : Coherent(_, String.order(SCon{Chr{y}, u}, SCon{Chr{z}, v}), String.order(SCon{Chr{x}, t}, SCon{Chr{z}, v}))
      %Equal.sym(Cmp, String.order(SCon{Chr{y}, u}, SCon{Chr{z}, v}), priority(U32.cmp(y, z), String.order(u, v)), string_cons(y, z, u, v)) : Coherent(priority(U32.cmp(x, y), String.order(t, u)), _, String.order(SCon{Chr{x}, t}, SCon{Chr{z}, v}))
      %Equal.sym(Cmp, String.order(SCon{Chr{x}, t}, SCon{Chr{z}, v}), priority(U32.cmp(x, z), String.order(t, v)), string_cons(x, z, t, v)) : Coherent(priority(U32.cmp(x, y), String.order(t, u)), priority(U32.cmp(y, z), String.order(u, v)), _)
      compose_orders(U32.cmp(x, y), U32.cmp(y, z), U32.cmp(x, z),
        String.order(t, u), String.order(u, v), String.order(t, v),
        u32_coherent(x, y, z), string_coherent(t, u, v))

law string_refl:
  for +s: String
  {String.order(s, s) == EQ{} : Cmp}
def string_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{x}, t}:
      %Equal.sym(Cmp, String.order.go(t, t, U32.cmp(x, x)), priority(U32.cmp(x, x), String.order(t, t)), string_go_priority(t, t, U32.cmp(x, x))) : {_ == EQ{} : Cmp}
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_refl(x)) : {priority(_, String.order(t, t)) == EQ{} : Cmp}
      string_refl(t)

law string_eq_refl:
  for s: String
  {String.eq(s, s) == True{} : Bool}
def string_eq_refl(s):
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), String.order(s, s), EQ{}, string_refl(s))

law cmp_lt:
  for c: Cmp
  for e: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}
def cmp_lt(c, e):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      F.absurd_boolean({EQ{} == LT{} : Cmp}, e)
    case GT{}:
      F.absurd_boolean({GT{} == LT{} : Cmp}, e)

law string_lt_trans:
  for +a: String
  for +b: String
  for +c: String
  for ab: {String.is_lt(a, b) == True{} : Bool}
  for bc: {String.is_lt(b, c) == True{} : Bool}
  {String.is_lt(a, c) == True{} : Bool}
def string_lt_trans(a, b, c, ab, bc):
  h1 = {(%cmp_lt(String.order(a, b), ab) : Coherent(_, String.order(b, c), String.order(a, c))
    string_coherent(a, b, c)) : Coherent(LT{}, String.order(b, c), String.order(a, c))}
  h2 = {(%cmp_lt(String.order(b, c), bc) : Coherent(LT{}, _, String.order(a, c))
    h1) : Coherent(LT{}, LT{}, String.order(a, c))}
  Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), String.order(a, c), LT{}, h2)

law string_lt_neq:
  for +a: String
  for +b: String
  for lt: {String.is_lt(a, b) == True{} : Bool}
  {String.eq(a, b) == False{} : Bool}
def string_lt_neq(a, b, lt):
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), String.order(a, b), LT{},
    cmp_lt(String.order(a, b), lt))

law cmp_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}
def cmp_eq(c, e):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      F.absurd_boolean({LT{} == EQ{} : Cmp}, e)
    case GT{}:
      F.absurd_boolean({GT{} == EQ{} : Cmp}, e)

def priority_equal(c: Cmp, -t: Cmp,
  e: {priority(c, t) == EQ{} : Cmp}) -> L.E<{c == EQ{} : Cmp}, {t == EQ{} : Cmp}>:
  match c:
    case EQ{}:
      L.Both{{==}, e}
    case LT{}:
      F.absurd_boolean(L.E<{LT{} == EQ{} : Cmp}, {t == EQ{} : Cmp}>,
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), LT{}, EQ{}, e))
    case GT{}:
      F.absurd_boolean(L.E<{GT{} == EQ{} : Cmp}, {t == EQ{} : Cmp}>,
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), GT{}, EQ{}, e))

def bool_equal(a: Bool, b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      F.absurd_boolean({False{} == True{} : Bool}, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), LT{}, EQ{}, e))
    case True{} False{}:
      F.absurd_boolean({True{} == False{} : Bool}, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), GT{}, EQ{}, e))

def word_fin_equal(+a: Bool, +b: Bool, +c: Cmp,
  e: {Word.cmp.fin(a, b, c) == EQ{} : Cmp}) -> L.E<{c == EQ{} : Cmp}, {a == b : Bool}>:
  F.combined_pair(L.E<{c == EQ{} : Cmp}, {a == b : Bool}>, {c == EQ{} : Cmp}, {Bool.cmp(a, b) == EQ{} : Cmp},
    priority_equal(c, Bool.cmp(a, b), Equal.trans(Cmp, priority(c, Bool.cmp(a, b)),
      Word.cmp.fin(a, b, c), EQ{}, Equal.sym(Cmp, Word.cmp.fin(a, b, c), priority(c, Bool.cmp(a, b)),
        word_fin_priority(a, b, c)), e)),
    tail => head => L.Both{tail, bool_equal(a, b, head)})

law word_equal:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}
def word_equal(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          F.combined_pair({WCon{ah, at} == WCon{bh, bt} : Word(1n+p)},
            {Word.cmp(p, at, bt) == EQ{} : Cmp}, {ah == bh : Bool},
            word_fin_equal(ah, bh, Word.cmp(p, at, bt), e),
            tail => head =>
              %head : {WCon{ah, at} == WCon{_, bt} : Word(1n+p)}
              Equal.cong(Word(p), Word(1n+p), t => WCon{ah, t}, at, bt, word_equal(p, at, bt, tail)))

law u32_equal:
  for a: U32
  for b: U32
  for e: {U32.cmp(a, b) == EQ{} : Cmp}
  {a == b : U32}
def u32_equal(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word_equal(32n, x, y, e))

law string_equal:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}
def string_equal(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{y}, u}:
      F.absurd_boolean({SNil{} == SCon{Chr{y}, u} : String}, e)
    case SCon{Chr{x}, t} SNil{}:
      F.absurd_boolean({SCon{Chr{x}, t} == SNil{} : String}, e)
    case SCon{Chr{x}, t} SCon{Chr{y}, u}:
      F.combined_pair({SCon{Chr{x}, t} == SCon{Chr{y}, u} : String},
        {U32.cmp(x, y) == EQ{} : Cmp}, {String.order(t, u) == EQ{} : Cmp},
        priority_equal(U32.cmp(x, y), String.order(t, u),
          Equal.trans(Cmp, priority(U32.cmp(x, y), String.order(t, u)),
            String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}), EQ{},
            Equal.sym(Cmp, String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}),
              priority(U32.cmp(x, y), String.order(t, u)), string_cons(x, y, t, u)),
            cmp_eq(String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}), e))),
        head => tail =>
          %u32_equal(x, y, head) : {SCon{Chr{x}, t} == SCon{Chr{_}, u} : String}
          Equal.cong(String, String, r => SCon{Chr{x}, r}, t, u,
            string_equal(t, u, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), String.order(t, u), EQ{}, tail))))

law string_eq_inverse:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {String.eq(b, a) == True{} : Bool}
def string_eq_inverse(a, b, e):
  %Equal.sym(String, a, b, string_equal(a, b, e)) : {String.eq(b, _) == True{} : Bool}
  string_eq_refl(b)
