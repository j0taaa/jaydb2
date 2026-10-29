# Fundamentos logicos do contrato JayDB.
# Cada `law` deste arquivo tem uma prova `def` com o mesmo nome.
# Nenhum destes lemas afirma a correcao de uma implementacao do banco.
import Base

type E<-P: Type, -Q: Type> is Type:
  Ambos{esq: P, dir: Q}

type Ou<-P: Type, -Q: Type> is Type:
  Esquerda{prova: P}
  Direita{prova: Q}

def Verdade() -> Type:
  Unit

def Falso() -> Type:
  Empty

def Implica(-P: Type, -Q: Type) -> Type:
  P -> Q

def Nao(-P: Type) -> Type:
  P -> Empty

def Verdadeiro(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# Conjuncao de TODAS as proposicoes P(x) da lista, sem filtragem.
def Todos(-A: Type, -P: @-x: A -> Type, xs: List<&1, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      E<P(h), Todos(A, P, t)>

# Prefixo usa igualdade proposicional dos elementos, nao um comparador
# booleano cuja correcao tivesse de ser pressuposta.
def Prefixo(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case x <> xt:
      match ys:
        case Nil{}:
          Empty
        case y <> yt:
          E<{x == y : A}, Prefixo(A, xt, yt)>

law verdade:
  Verdade()

def verdade():
  Unit{}

law e_intro:
  for -P: Type
  for -Q: Type
  for p: P
  for q: Q
  E<P, Q>

def e_intro(P, Q, p, q):
  Ambos{p, q}

law e_esquerda:
  for -P: Type
  for -Q: Type
  for pq: E<P, Q>
  P

def e_esquerda(P, Q, pq):
  match pq:
    case Ambos{p, q}:
      p

law e_direita:
  for -P: Type
  for -Q: Type
  for pq: E<P, Q>
  Q

def e_direita(P, Q, pq):
  match pq:
    case Ambos{p, q}:
      q

law e_comuta:
  for -P: Type
  for -Q: Type
  for pq: E<P, Q>
  E<Q, P>

def e_comuta(P, Q, pq):
  match pq:
    case Ambos{p, q}:
      Ambos{q, p}

law e_associa:
  for -P: Type
  for -Q: Type
  for -R: Type
  for pqr: E<E<P, Q>, R>
  E<P, E<Q, R>>

def e_associa(P, Q, R, pqr):
  match pqr:
    case Ambos{pq, r}:
      match pq:
        case Ambos{p, q}:
          Ambos{p, Ambos{q, r}}

law ou_esquerda:
  for -P: Type
  for -Q: Type
  for p: P
  Ou<P, Q>

def ou_esquerda(P, Q, p):
  Esquerda{p}

law ou_direita:
  for -P: Type
  for -Q: Type
  for q: Q
  Ou<P, Q>

def ou_direita(P, Q, q):
  Direita{q}

law ou_elimina:
  for -P: Type
  for -Q: Type
  for -R: Type
  for alternativa: Ou<P, Q>
  for de_p: P -> R
  for de_q: Q -> R
  R

def ou_elimina(P, Q, R, alternativa, de_p, de_q):
  match alternativa:
    case Esquerda{p}:
      de_p(p)
    case Direita{q}:
      de_q(q)

law modus_ponens:
  for -P: Type
  for -Q: Type
  for implicacao: Implica(P, Q)
  for p: P
  Q

def modus_ponens(P, Q, implicacao, p):
  implicacao(p)

law ex_falso:
  for -P: Type
  for impossivel: Falso()
  P

def ex_falso(P, impossivel):
  match impossivel:

law todos_vazia:
  for -A: Type
  for -P: @-x: A -> Type
  Todos(A, P, Nil{})

def todos_vazia(A, P):
  Unit{}

law todos_cons:
  for -A: Type
  for -P: @-x: A -> Type
  for -h: A
  for -t: List<&1, A>
  for ph: P(h)
  for pt: Todos(A, P, t)
  Todos(A, P, h <> t)

def todos_cons(A, P, h, t, ph, pt):
  Ambos{ph, pt}

law todos_cabeca:
  for -A: Type
  for -P: @-x: A -> Type
  for -h: A
  for -t: List<&1, A>
  for todas: Todos(A, P, h <> t)
  P(h)

def todos_cabeca(A, P, h, t, todas):
  match todas:
    case Ambos{ph, pt}:
      ph

law todos_cauda:
  for -A: Type
  for -P: @-x: A -> Type
  for -h: A
  for -t: List<&1, A>
  for todas: Todos(A, P, h <> t)
  Todos(A, P, t)

def todos_cauda(A, P, h, t, todas):
  match todas:
    case Ambos{ph, pt}:
      pt

law prefixo_vazio:
  for -A: Data
  for -xs: List<&2, A>
  Prefixo(A, Nil{}, xs)

def prefixo_vazio(A, xs):
  Unit{}

law prefixo_refl:
  for -A: Data
  for xs: List<&2, A>
  Prefixo(A, xs, xs)

def prefixo_refl(A, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      Ambos{{==}, prefixo_refl(A, t)}
