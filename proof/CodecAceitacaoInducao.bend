# Tipos das fases de UMA recursao lexicografica. O comprimento e apenas
# matematico; nao e uma quota adicional recebida pelo decoder.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./CodecPercurso.bend as R
import ./CodecAceitacaoFilhos.bend as H
import ./CodecAceitacaoPrefixo.bend as X
import ./CodecLimitesSequencias.bend as S
import ./CodecAceitacaoRegistro.bend as G

def Obrigacao(n: Nat, fase: Nat, xs: List<&2, S.ValorSegmentado>, ys: List<&2, S.CampoSegmentado>,
  +bs: List<&2, U32>, corpo: B.Numero64, teto: B.Numero64, v: D.Valor) -> Type:
  match fase:
    case 0n:
      L.E<{Nat.is_le(B.comprimento(bs), n) == True{} : Bool},
        L.E<{B.octetos_validos(bs) == True{} : Bool},
          {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}>>
    case 1n:
      L.E<H.FilhosLidos(xs, n), {B.octetos_validos(S.bytes_valores(xs)) == True{} : Bool}>
    case 2n:
      L.E<G.CamposLidos(ys, n), {B.octetos_validos(S.bytes_campos(ys)) == True{} : Bool}>
    case 3n+p:
      Unit

def Conclusao(fase: Nat, xs: List<&2, S.ValorSegmentado>, ys: List<&2, S.CampoSegmentado>,
  bs: List<&2, U32>, v: D.Valor) -> Type:
  match fase:
    case 0n:
      P.Codificacao(v, bs)
    case 1n:
      S.ValoresCanonicos(xs)
    case 2n:
      S.CamposCanonicos(ys)
    case 3n+p:
      Unit
