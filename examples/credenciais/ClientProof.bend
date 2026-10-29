import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Livre.bend as L
import ./Terminacao.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificado(s, valido, identidade, n):
  L.percurso_livre_cobre_prefixos_e_final(
    S.executar(n, Client.programa(), C.esquema(), s, I.contexto(), I.argumentos()),
    C.esquema(), C.limites(), S.ambiente(I.config()), s, I.contexto(), B.codigo(), I.argumentos())

def retorno_finito(r: S.Retorno) -> T.Finita(1n, Client.responder(r)):
  match r:
    case S.Unidade{}:
      Unit{}
    case S.Dado{obs}:
      match obs:
        case D.LinhaAusente{}:
          Unit{}
        case D.Celula{v}:
          Unit{}
        case D.Existencia{b}:
          Unit{}
        case D.Quantidade{n}:
          Unit{}
        case D.Chaves{xs}:
          Unit{}

def finito(ctx: D.Contexto, args: D.Valor) ->
  T.Finita(4n, S.iniciar(Client.programa(), ctx, args)):
  match ctx:
    case D.Contexto{id, tipo}:
      r1 => r2 => r3 => retorno_finito(r3)

def B.termina(s, ctx, args):
  +contexto = ctx
  +argumentos = args
  T.programa_finito(4n, Client.programa(), C.esquema(), s, contexto, argumentos,
    finito(contexto, argumentos))
