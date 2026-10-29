# Pacote interno: u64 do primeiro bloco, primeiro bloco e segundo bloco.
# Nao e uma extensao do protocolo publico; nunca e entregue ao programa.
import Base
import ../contrato/Bytes.bend as B
import ./Codec.bend as C

type Partes is Data:
  Partes{primeira: List<&2, U32>, segunda: List<&2, U32>}

def inverter(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      inverter(t, Con{h, acc})

def desviar(zero: Bool, parar: Unit -> Maybe<&2, Partes>,
  continuar: Unit -> Maybe<&2, Partes>) -> Maybe<&2, Partes>:
  match zero:
    case True{}:
      parar(Unit{})
    case False{}:
      continuar(Unit{})

def vazio(zero: Bool, xs: List<&2, U32>) -> Maybe<&2, Partes>:
  match zero:
    case True{}:
      Some{Partes{inverter(xs, Nil{}), Nil{}}}
    case False{}:
      None{}

def cortar(bytes: List<&2, U32>, +quantidade: B.Numero64,
  +invertidos: List<&2, U32>) -> Maybe<&2, Partes>:
  match bytes:
    case Nil{}:
      vazio(C.zero64(quantidade), invertidos)
    case Con{+h, +t}:
      desviar(C.zero64(quantidade),
        unidade => Some{Partes{inverter(invertidos, Nil{}), Con{h, t}}},
        unidade => cortar(t, C.diminuir64(quantidade), Con{h, invertidos}))

def palavra(a: U32, b: U32, c: U32, d: U32) -> U32:
  (a * 16777216 + b * 65536 + c * 256 + d : U32)

def cabecalho(bytes: List<&2, U32>) -> Maybe<&2, Partes>:
  match bytes:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}}}}:
      cortar(resto, B.Numero64{palavra(a, b, c, d), palavra(e, f, g, h)}, Nil{})
    case _:
      None{}

def validar(ok: Bool, bytes: List<&2, U32>) -> Maybe<&2, Partes>:
  match ok:
    case False{}:
      None{}
    case True{}:
      cabecalho(bytes)

def separar(+bytes: List<&2, U32>) -> Maybe<&2, Partes>:
  validar(B.octetos_validos(bytes), bytes)

def juntar_com_cabecalho(cabecalho: Maybe<&2, List<&2, U32>>,
  primeira: List<&2, U32>, segunda: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match cabecalho:
    case None{}:
      None{}
    case Some{header}:
      Some{B.concatenar(header, B.concatenar(primeira, segunda))}

def juntar(+primeira: List<&2, U32>, segunda: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  juntar_com_cabecalho(B.comprimento64(B.comprimento(primeira)), primeira, segunda)

law cabecalho_incompleto_nao_produz_blocos:
  {separar([0, 0, 0, 0, 0, 0, 0]) == None{} : Maybe<&2, Partes>}
def cabecalho_incompleto_nao_produz_blocos():
  {==}

law separa_sem_consumir_segundo_bloco:
  {separar([0, 0, 0, 0, 0, 0, 0, 2, 255, 0, 7, 8]) ==
    Some{Partes{[255, 0], [7, 8]}} : Maybe<&2, Partes>}
def separa_sem_consumir_segundo_bloco():
  {==}

law bloco_truncado_nao_vira_bloco_menor:
  {separar([0, 0, 0, 0, 0, 0, 0, 2, 255]) == None{} : Maybe<&2, Partes>}
def bloco_truncado_nao_vira_bloco_menor():
  {==}
