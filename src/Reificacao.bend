# Transporte de argumentos publicos para a fonte verificada. Um literal de
# texto representa octetos como escalares 0..255; nao aplica UTF-8 novamente.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ./Codec.bend as C

def texto(bytes: List<&2, U32>) -> String:
  match bytes:
    case Nil{}:
      SNil{}
    case Con{b, resto}:
      SCon{Chr{b}, texto(resto)}

def octetos(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{b}, resto}:
      Con{b, octetos(resto)}

def extrair(resultado: C.Resultado) -> Maybe<&2, D.Valor>:
  match resultado:
    case C.Decodificado{valor}:
      Some{valor}
    case _:
      None{}

def decodificar(s: String, alto: U32, baixo: U32) -> Maybe<&2, D.Valor>:
  extrair(C.decodificar(octetos(s), B.Numero64{alto, baixo}))

# O gerador fornece somente codificacoes admitidas, cuja recuperacao exata
# e demonstrada em proof/Reificacao.bend. None nao fornece dados do banco.
def valor(resultado: Maybe<&2, D.Valor>) -> D.Valor:
  match resultado:
    case Some{v}:
      v
    case None{}:
      D.VAusente{}

def argumentos(s: String, alto: U32, baixo: U32) -> D.Valor:
  valor(decodificar(s, alto, baixo))

law octetos_nao_reaplicam_utf8:
  {octetos(texto([0, 127, 128, 255])) == [0, 127, 128, 255] : List<&2, U32>}
def octetos_nao_reaplicam_utf8():
  {==}
