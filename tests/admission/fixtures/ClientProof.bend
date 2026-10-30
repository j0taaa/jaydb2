import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Logica.bend as L
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificado(s, valido, identidade, n):
  match n:
    case 0n:
      L.Ambos{L.Ambos{{==}, Unit{}}, L.Ambos{{==}, Unit{}}}
    case 1n+m:
      match m:
        case 0n:
          L.Ambos{L.Ambos{L.Ambos{{==}, Unit{}}, L.Ambos{{==}, Unit{}}},
            L.Ambos{L.Ambos{{==}, Unit{}}, Unit{}}}
        case 1n+k:
          L.Ambos{L.Ambos{L.Ambos{{==}, Unit{}}, L.Ambos{{==}, Unit{}}},
            L.Ambos{L.Ambos{{==}, Unit{}}, Unit{}}}

def B.termina(s, ctx, args):
  (1n, s, Nil{}, S.Resposta{S.Recusa{}, D.VInt{0, 6}}, {==})
