# Testemunhas de filhos extraidas do parser, sem canonicidade presumida.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecAceitacaoPrefixo.bend as X
import ./CodecLimitesNomes.bend as N
import ./CodecLimitesSequencias.bend as S

type FilhoLido<-v: D.Valor, -bs: List<&2, U32>, -max: Nat> is Type:
  FilhoLido{corpo: B.Numero64, teto: B.Numero64, fora: C.Pilha,
    local: {R.maquina(X.executar_local(bs, fora, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina},
    bound: {Nat.is_le(B.comprimento(bs), max) == True{} : Bool}}

def FilhosLidos(xs: List<&2, S.ValorSegmentado>, +max: Nat) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.ValorSegmentado{v, bs}, t}:
      L.E<FilhoLido<v, bs, max>, FilhosLidos(t, max)>

def BytesPositivos(bs: List<&2, U32>) -> Type:
  match bs:
    case Nil{}:
      Empty
    case Con{b, t}:
      Unit

law tag_raiz_local_aceito_tem_bytes:
  for +bs: List<&2, U32>
  for +fora: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {R.maquina(X.executar_local(bs, fora, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
  BytesPositivos(bs)
def tag_raiz_local_aceito_tem_bytes(bs, fora, corpo, teto, v, aceito):
  match bs:
    case Nil{}:
      F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => X.e_pronto(m), C.Tag{C.Raiz{}}, C.Pronto{v}, aceito))
    case Con{b, t}:
      Unit{}

def limite_de_bytes_iguais(+a: List<&2, U32>, +b: List<&2, U32>, +n: Nat,
  bytes: {a == b : List<&2, U32>}, limite: {Nat.is_le(B.comprimento(a), n) == True{} : Bool}) ->
  {Nat.is_le(B.comprimento(b), n) == True{} : Bool}:
  %bytes : {Nat.is_le(B.comprimento(_), n) == True{} : Bool}
  limite

law limite_prefixo:
  for +pre: List<&2, U32>
  for +suf: List<&2, U32>
  for +n: Nat
  for limite: {Nat.is_le(B.comprimento(B.concatenar(pre, suf)), n) == True{} : Bool}
  {Nat.is_le(B.comprimento(pre), n) == True{} : Bool}
def limite_prefixo(pre, suf, n, limite):
  match pre n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{b, t} 0n:
      F.absurdo_booleano({False{} == True{} : Bool}, limite)
    case Con{b, +t} 1n+p:
      limite_prefixo(t, suf, p, limite)

law limite_sufixo:
  for +pre: List<&2, U32>
  for +suf: List<&2, U32>
  for +n: Nat
  for limite: {Nat.is_le(B.comprimento(B.concatenar(pre, suf)), n) == True{} : Bool}
  {Nat.is_le(B.comprimento(suf), n) == True{} : Bool}
def limite_sufixo(pre, suf, n, limite):
  match pre n:
    case Nil{} _:
      limite
    case Con{b, t} 0n:
      F.absurdo_booleano({Nat.is_le(B.comprimento(suf), 0n) == True{} : Bool}, limite)
    case Con{b, +t} 1n+p:
      N.aumentar_limite_direito(B.comprimento(suf), p, limite_sufixo(t, suf, p, limite))

law sufixo_apos_prefixo_positivo:
  for +pre: List<&2, U32>
  for +suf: List<&2, U32>
  for +n: Nat
  for positivo: BytesPositivos(pre)
  for limite: {Nat.is_le(B.comprimento(B.concatenar(pre, suf)), 1n+n) == True{} : Bool}
  {Nat.is_le(B.comprimento(suf), n) == True{} : Bool}
def sufixo_apos_prefixo_positivo(pre, suf, n, positivo, limite):
  match pre:
    case Nil{}:
      L.ex_falso({Nat.is_le(B.comprimento(suf), n) == True{} : Bool}, positivo)
    case Con{b, +t}:
      limite_sufixo(t, suf, n, limite)
