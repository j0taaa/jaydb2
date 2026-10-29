# Algebra geral das comparacoes reais de Base, usada para o cadastro.
import Base
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F

def prioridade(primeiro: Cmp, segundo: Cmp) -> Cmp:
  match primeiro:
    case EQ{}:
      segundo
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# Transitividade e substituicao por iguais em uma unica proposicao.
def Coerente(ab: Cmp, bc: Cmp, ac: Cmp) -> Type:
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

def esquerda_lt(c: Cmp) -> Coerente(c, LT{}, LT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      Unit{}

def esquerda_gt(c: Cmp) -> Coerente(c, GT{}, GT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Unit{}
    case GT{}:
      {==}

def direita_lt(c: Cmp) -> Coerente(LT{}, c, LT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      Unit{}

def direita_gt(c: Cmp) -> Coerente(GT{}, c, GT{}):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Unit{}
    case GT{}:
      {==}

law compor_ordens:
  for ab: Cmp
  for bc: Cmp
  for -ac: Cmp
  for xy: Cmp
  for yz: Cmp
  for -xz: Cmp
  for h: Coerente(ab, bc, ac)
  for t: Coerente(xy, yz, xz)
  Coerente(prioridade(ab, xy), prioridade(bc, yz), prioridade(ac, xz))
def compor_ordens(ab, bc, ac, xy, yz, xz, h, t):
  match ab bc:
    case EQ{} EQ{}:
      %Equal.sym(Cmp, ac, EQ{}, h) : Coerente(xy, yz, prioridade(_, xz))
      t
    case EQ{} LT{}:
      %Equal.sym(Cmp, ac, LT{}, h) : Coerente(xy, LT{}, prioridade(_, xz))
      esquerda_lt(xy)
    case EQ{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : Coerente(xy, GT{}, prioridade(_, xz))
      esquerda_gt(xy)
    case LT{} EQ{}:
      %Equal.sym(Cmp, ac, LT{}, h) : Coerente(LT{}, yz, prioridade(_, xz))
      direita_lt(yz)
    case GT{} EQ{}:
      %Equal.sym(Cmp, ac, GT{}, h) : Coerente(GT{}, yz, prioridade(_, xz))
      direita_gt(yz)
    case LT{} LT{}:
      %Equal.sym(Cmp, ac, LT{}, h) : Coerente(LT{}, LT{}, prioridade(_, xz))
      {==}
    case GT{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : Coerente(GT{}, GT{}, prioridade(_, xz))
      {==}
    case LT{} GT{}:
      Unit{}
    case GT{} LT{}:
      Unit{}

law bool_coerente:
  for a: Bool
  for b: Bool
  for c: Bool
  Coerente(Bool.cmp(a, b), Bool.cmp(b, c), Bool.cmp(a, c))
def bool_coerente(a, b, c):
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

law word_fin_prioridade:
  for a: Bool
  for b: Bool
  for c: Cmp
  {Word.cmp.fin(a, b, c) == prioridade(c, Bool.cmp(a, b)) : Cmp}
def word_fin_prioridade(a, b, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law word_coerente:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  Coerente(Word.cmp(n, a, b), Word.cmp(n, b, c), Word.cmp(n, a, c))
def word_coerente(n, a, b, c):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b c:
        case WCon{ah, at} WCon{bh, bt} WCon{ch, ct}:
          %Equal.sym(Cmp, Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)),
            prioridade(Word.cmp(p, at, bt), Bool.cmp(ah, bh)),
            word_fin_prioridade(ah, bh, Word.cmp(p, at, bt))) : Coerente(_, Word.cmp(1n+p, WCon{bh, bt}, WCon{ch, ct}), Word.cmp(1n+p, WCon{ah, at}, WCon{ch, ct}))
          %Equal.sym(Cmp, Word.cmp.fin(bh, ch, Word.cmp(p, bt, ct)),
            prioridade(Word.cmp(p, bt, ct), Bool.cmp(bh, ch)),
            word_fin_prioridade(bh, ch, Word.cmp(p, bt, ct))) : Coerente(prioridade(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), _, Word.cmp(1n+p, WCon{ah, at}, WCon{ch, ct}))
          %Equal.sym(Cmp, Word.cmp.fin(ah, ch, Word.cmp(p, at, ct)),
            prioridade(Word.cmp(p, at, ct), Bool.cmp(ah, ch)),
            word_fin_prioridade(ah, ch, Word.cmp(p, at, ct))) : Coerente(prioridade(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), prioridade(Word.cmp(p, bt, ct), Bool.cmp(bh, ch)), _)
          compor_ordens(Word.cmp(p, at, bt), Word.cmp(p, bt, ct), Word.cmp(p, at, ct),
            Bool.cmp(ah, bh), Bool.cmp(bh, ch), Bool.cmp(ah, ch),
            word_coerente(p, at, bt, ct), bool_coerente(ah, bh, ch))

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

law u32_coerente:
  for a: U32
  for b: U32
  for c: U32
  Coerente(U32.cmp(a, b), U32.cmp(b, c), U32.cmp(a, c))
def u32_coerente(a, b, c):
  match a b c:
    case U32{x} U32{y} U32{z}:
      word_coerente(32n, x, y, z)

law u32_refl:
  for a: U32
  {U32.cmp(a, a) == EQ{} : Cmp}
def u32_refl(a):
  match a:
    case U32{x}:
      word_refl(32n, x)

law string_go_prioridade:
  for a: String
  for b: String
  for c: Cmp
  {String.order.go(a, b, c) == prioridade(c, String.order(a, b)) : Cmp}
def string_go_prioridade(a, b, c):
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
    prioridade(U32.cmp(x, y), String.order(a, b)) : Cmp}
def string_cons(x, y, a, b):
  string_go_prioridade(a, b, U32.cmp(x, y))

law string_coerente:
  for +a: String
  for +b: String
  for +c: String
  Coerente(String.order(a, b), String.order(b, c), String.order(a, c))
def string_coerente(a, b, c):
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
      direita_lt(String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}))
    case SCon{Chr{x}, t} SNil{} SCon{Chr{y}, u}:
      Unit{}
    case SCon{Chr{x}, t} SCon{Chr{y}, u} SNil{}:
      esquerda_gt(String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}))
    case SCon{Chr{x}, t} SCon{Chr{y}, u} SCon{Chr{z}, v}:
      %Equal.sym(Cmp, String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}), prioridade(U32.cmp(x, y), String.order(t, u)), string_cons(x, y, t, u)) : Coerente(_, String.order(SCon{Chr{y}, u}, SCon{Chr{z}, v}), String.order(SCon{Chr{x}, t}, SCon{Chr{z}, v}))
      %Equal.sym(Cmp, String.order(SCon{Chr{y}, u}, SCon{Chr{z}, v}), prioridade(U32.cmp(y, z), String.order(u, v)), string_cons(y, z, u, v)) : Coerente(prioridade(U32.cmp(x, y), String.order(t, u)), _, String.order(SCon{Chr{x}, t}, SCon{Chr{z}, v}))
      %Equal.sym(Cmp, String.order(SCon{Chr{x}, t}, SCon{Chr{z}, v}), prioridade(U32.cmp(x, z), String.order(t, v)), string_cons(x, z, t, v)) : Coerente(prioridade(U32.cmp(x, y), String.order(t, u)), prioridade(U32.cmp(y, z), String.order(u, v)), _)
      compor_ordens(U32.cmp(x, y), U32.cmp(y, z), U32.cmp(x, z),
        String.order(t, u), String.order(u, v), String.order(t, v),
        u32_coerente(x, y, z), string_coerente(t, u, v))

law string_refl:
  for +s: String
  {String.order(s, s) == EQ{} : Cmp}
def string_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{x}, t}:
      %Equal.sym(Cmp, String.order.go(t, t, U32.cmp(x, x)), prioridade(U32.cmp(x, x), String.order(t, t)), string_go_prioridade(t, t, U32.cmp(x, x))) : {_ == EQ{} : Cmp}
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_refl(x)) : {prioridade(_, String.order(t, t)) == EQ{} : Cmp}
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
      F.absurdo_booleano({EQ{} == LT{} : Cmp}, e)
    case GT{}:
      F.absurdo_booleano({GT{} == LT{} : Cmp}, e)

law string_lt_trans:
  for +a: String
  for +b: String
  for +c: String
  for ab: {String.is_lt(a, b) == True{} : Bool}
  for bc: {String.is_lt(b, c) == True{} : Bool}
  {String.is_lt(a, c) == True{} : Bool}
def string_lt_trans(a, b, c, ab, bc):
  h1 = {(%cmp_lt(String.order(a, b), ab) : Coerente(_, String.order(b, c), String.order(a, c))
    string_coerente(a, b, c)) : Coerente(LT{}, String.order(b, c), String.order(a, c))}
  h2 = {(%cmp_lt(String.order(b, c), bc) : Coerente(LT{}, _, String.order(a, c))
    h1) : Coerente(LT{}, LT{}, String.order(a, c))}
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
      F.absurdo_booleano({LT{} == EQ{} : Cmp}, e)
    case GT{}:
      F.absurdo_booleano({GT{} == EQ{} : Cmp}, e)

def prioridade_igual(c: Cmp, -t: Cmp,
  e: {prioridade(c, t) == EQ{} : Cmp}) -> L.E<{c == EQ{} : Cmp}, {t == EQ{} : Cmp}>:
  match c:
    case EQ{}:
      L.Ambos{{==}, e}
    case LT{}:
      F.absurdo_booleano(L.E<{LT{} == EQ{} : Cmp}, {t == EQ{} : Cmp}>,
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), LT{}, EQ{}, e))
    case GT{}:
      F.absurdo_booleano(L.E<{GT{} == EQ{} : Cmp}, {t == EQ{} : Cmp}>,
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), GT{}, EQ{}, e))

def bool_igual(a: Bool, b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      F.absurdo_booleano({False{} == True{} : Bool}, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), LT{}, EQ{}, e))
    case True{} False{}:
      F.absurdo_booleano({True{} == False{} : Bool}, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), GT{}, EQ{}, e))

def word_fin_igual(+a: Bool, +b: Bool, +c: Cmp,
  e: {Word.cmp.fin(a, b, c) == EQ{} : Cmp}) -> L.E<{c == EQ{} : Cmp}, {a == b : Bool}>:
  F.com_par(L.E<{c == EQ{} : Cmp}, {a == b : Bool}>, {c == EQ{} : Cmp}, {Bool.cmp(a, b) == EQ{} : Cmp},
    prioridade_igual(c, Bool.cmp(a, b), Equal.trans(Cmp, prioridade(c, Bool.cmp(a, b)),
      Word.cmp.fin(a, b, c), EQ{}, Equal.sym(Cmp, Word.cmp.fin(a, b, c), prioridade(c, Bool.cmp(a, b)),
        word_fin_prioridade(a, b, c)), e)),
    cauda => cabeca => L.Ambos{cauda, bool_igual(a, b, cabeca)})

law word_igual:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}
def word_igual(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          F.com_par({WCon{ah, at} == WCon{bh, bt} : Word(1n+p)},
            {Word.cmp(p, at, bt) == EQ{} : Cmp}, {ah == bh : Bool},
            word_fin_igual(ah, bh, Word.cmp(p, at, bt), e),
            cauda => cabeca =>
              %cabeca : {WCon{ah, at} == WCon{_, bt} : Word(1n+p)}
              Equal.cong(Word(p), Word(1n+p), t => WCon{ah, t}, at, bt, word_igual(p, at, bt, cauda)))

law u32_igual:
  for a: U32
  for b: U32
  for e: {U32.cmp(a, b) == EQ{} : Cmp}
  {a == b : U32}
def u32_igual(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word_igual(32n, x, y, e))

law string_igual:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}
def string_igual(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{y}, u}:
      F.absurdo_booleano({SNil{} == SCon{Chr{y}, u} : String}, e)
    case SCon{Chr{x}, t} SNil{}:
      F.absurdo_booleano({SCon{Chr{x}, t} == SNil{} : String}, e)
    case SCon{Chr{x}, t} SCon{Chr{y}, u}:
      F.com_par({SCon{Chr{x}, t} == SCon{Chr{y}, u} : String},
        {U32.cmp(x, y) == EQ{} : Cmp}, {String.order(t, u) == EQ{} : Cmp},
        prioridade_igual(U32.cmp(x, y), String.order(t, u),
          Equal.trans(Cmp, prioridade(U32.cmp(x, y), String.order(t, u)),
            String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}), EQ{},
            Equal.sym(Cmp, String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}),
              prioridade(U32.cmp(x, y), String.order(t, u)), string_cons(x, y, t, u)),
            cmp_eq(String.order(SCon{Chr{x}, t}, SCon{Chr{y}, u}), e))),
        cabeca => cauda =>
          %u32_igual(x, y, cabeca) : {SCon{Chr{x}, t} == SCon{Chr{_}, u} : String}
          Equal.cong(String, String, r => SCon{Chr{x}, r}, t, u,
            string_igual(t, u, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), String.order(t, u), EQ{}, cauda))))

law string_eq_inverso:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {String.eq(b, a) == True{} : Bool}
def string_eq_inverso(a, b, e):
  %Equal.sym(String, a, b, string_igual(a, b, e)) : {String.eq(b, _) == True{} : Bool}
  string_eq_refl(b)
