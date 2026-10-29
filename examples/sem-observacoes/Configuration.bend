import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Environment.bend as E

# Exemplo de uma lei proposicional: programas desta instancia nao acessam dados.
# O cadastro continua existindo e a autenticacao e feita pelo nucleo.
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
    S.Limites{32768n, 65536n, 32768n}, E.identidade()}
