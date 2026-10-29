import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Logica.bend as L
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def publicacao_inalterada(r: S.Resposta, -s: D.Estado,
  valido: R.Valido(I.config(), s)) -> R.PublicacaoValida(r, I.config(), s):
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      valido
    case S.Resposta{S.Recusa{}, v}:
      Unit{}
    case S.Resposta{S.Entrada{}, v}:
      Unit{}
    case S.Resposta{S.Autenticacao{}, v}:
      Unit{}
    case S.Resposta{S.Certificado{}, v}:
      Unit{}
    case S.Resposta{S.Dados{}, v}:
      Unit{}
    case S.Resposta{S.Limite{}, v}:
      Unit{}
    case S.Resposta{S.Falha{}, v}:
      Unit{}

def prefixo(-s: D.Estado) -> R.SegurancaPrefixo(I.config(), s,
  I.contexto(), B.codigo(), I.argumentos(), s, Nil{}):
  L.Ambos{L.Ambos{{==}, Unit{}},
    L.Ambos{L.Ambos{{==}, Unit{}}, L.Ambos{{==}, Unit{}}}}

def final(s: D.Estado, valido: R.Valido(I.config(), s)) ->
  R.SegurancaFinal(I.config(), s, I.contexto(), B.codigo(), I.argumentos(), s,
    Nil{}, R.finalizar(S.Resposta{S.Sucesso{}, D.VInt{0, 6}}, I.config(), s)):
  L.Ambos{L.Ambos{{==}, Unit{}},
    publicacao_inalterada(R.finalizar(S.Resposta{S.Sucesso{}, D.VInt{0, 6}}, I.config(), s), s, valido)}

def B.certificado(s, valido, identidade, n):
  match n:
    case 0n:
      prefixo(s)
    case 1n+m:
      match m:
        case 0n:
          L.Ambos{prefixo(s), final(s, valido)}
        case 1n+k:
          L.Ambos{prefixo(s), final(s, valido)}

def B.termina(s, ctx, args):
  (1n, s, Nil{}, S.Resposta{S.Sucesso{}, D.VInt{0, 6}}, {==})
