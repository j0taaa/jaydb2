# Lemas construtivos usados pelas provas da implementacao. Sem axiomas.
import Base
import ../contrato/Logica.bend as L

def com_par(-A: Type, -P: Type, -Q: Type, par: L.E<P, Q>,
  continuar: P -> Q -> A) -> A:
  match par:
    case L.Ambos{p, q}:
      continuar(p, q)

def falso_nao_verdadeiro(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def absurdo_booleano(-A: Type, e: {False{} == True{} : Bool}) -> A:
  L.ex_falso(A, falso_nao_verdadeiro(e))

law e_booleano_esquerda:
  for a: Bool
  for -b: Bool
  for e: {a && b == True{} : Bool}
  {a == True{} : Bool}
def e_booleano_esquerda(a, b, e):
  match a:
    case False{}:
      absurdo_booleano({False{} == True{} : Bool}, e)
    case True{}:
      {==}

law e_booleano_direita:
  for a: Bool
  for -b: Bool
  for e: {a && b == True{} : Bool}
  {b == True{} : Bool}
def e_booleano_direita(a, b, e):
  match a:
    case False{}:
      absurdo_booleano({b == True{} : Bool}, e)
    case True{}:
      e

law e_booleano_separar:
  for a: Bool
  for -b: Bool
  for e: {a && b == True{} : Bool}
  L.E<{a == True{} : Bool}, {b == True{} : Bool}>
def e_booleano_separar(a, b, e):
  match a:
    case False{}:
      absurdo_booleano(L.E<{False{} == True{} : Bool}, {b == True{} : Bool}>, e)
    case True{}:
      L.Ambos{{==}, e}

law e_booleano_intro:
  for -a: Bool
  for -b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {a && b == True{} : Bool}
def e_booleano_intro(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {_ && b == True{} : Bool}
  eb

law negacao_verdadeira:
  for b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}
def negacao_verdadeira(b, e):
  match b:
    case False{}:
      {==}
    case True{}:
      absurdo_booleano({True{} == False{} : Bool}, e)

def algum(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def nenhum_nao_algum(-A: Data, -x: A,
  e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  falso_nao_verdadeiro(Equal.cong(Maybe<&2, A>, Bool, m => algum(A, m),
    None{}, Some{x}, e))

def extrair_ou(-A: Data, m: Maybe<&2, A>, padrao: A) -> A:
  match m:
    case None{}:
      padrao
    case Some{x}:
      x

law algum_injetivo:
  for -A: Data
  for +a: A
  for -b: A
  for e: {Some{a} == Some{b} : Maybe<&2, A>}
  {a == b : A}
def algum_injetivo(A, a, b, e):
  Equal.cong(Maybe<&2, A>, A,
    m => extrair_ou(A, m, a),
    Some{a}, Some{b}, e)

law prefixo_transitivo:
  for -A: Data
  for xs: List<&2, A>
  for ys: List<&2, A>
  for zs: List<&2, A>
  for xy: L.Prefixo(A, xs, ys)
  for yz: L.Prefixo(A, ys, zs)
  L.Prefixo(A, xs, zs)
def prefixo_transitivo(A, xs, ys, zs, xy, yz):
  match xs ys zs:
    case Nil{} _ _:
      Unit{}
    case Con{x, xt} Nil{} _:
      match xy:
    case Con{x, xt} Con{y, yt} Nil{}:
      match yz:
    case Con{x, xt} Con{y, yt} Con{z, zt}:
      match xy yz:
        case L.Ambos{cabeca1, cauda1} L.Ambos{cabeca2, cauda2}:
          L.Ambos{Equal.trans(A, x, y, z, cabeca1, cabeca2),
            prefixo_transitivo(A, xt, yt, zt, cauda1, cauda2)}
