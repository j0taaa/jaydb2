import Base
import ./Dados.bend as D
import ./Semantica.bend as S

def NaoObserva(h: S.Situacao) -> Type:
  match h:
    case S.Estavel{s}:
      Unit
    case S.Executando{s, c, p, a, w, ts}:
      {ts == Nil{} : List<&2, S.Evento>}
    case S.Encerrada{s, c, p, a, w, ts, r}:
      {ts == Nil{} : List<&2, S.Evento>}

def config() -> S.Configuracao:
  S.Configuracao{D.Esquema{Nil{}}, S.MaisUmaLei{NaoObserva, S.NenhumaLei{}},
    S.Limites{256n, 256n, 256n}, "Bend-2.0.39-CPU"}

def contexto() -> D.Contexto:
  D.Contexto{"alice", "usuario"}

def argumentos() -> D.Valor:
  D.VInt{0, 42}
