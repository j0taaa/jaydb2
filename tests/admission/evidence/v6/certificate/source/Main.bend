import Base
import ./ClientProof.bend as Proof
import ./Client.bend as Client
import ./Instance.bend as I
import ./Dados.bend as D
import ./Semantica.bend as S

def resultado(a: S.Acao) -> D.Valor:
  match a:
    case S.Recusar{v}:
      v
    case _:
      D.VAusente{}

def main() -> D.Valor:
  resultado(S.iniciar(Client.programa(), I.contexto(), I.argumentos()))
