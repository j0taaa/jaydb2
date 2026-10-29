import Base
import ../../contrato/LAWS.bend as Leis
import ../../contrato/Interface.bend as I
import ../../contrato/Recursos.bend as X
import ../../contrato/Semantica.bend as S
import ../../contrato/Requisitos.bend as R
import ../../contrato/Dados.bend as D
import ../../contrato/Bytes.bend as B
import ../../proof/RecepcaoLimites.bend as Q

# Nao recebe LeituraLimitada como premissa: a constroi do limite de consumo
# real do syscall, da admissao do header e de sua representacao exata.
law read_confirmado_satisfaz_regra_original_para_qualquer_corpo:
  for -a: I.Ambiente
  for -k: String
  for -t: Nat
  for -mundo: Nat
  for c: S.Configuracao
  for -s: D.Estado
  for +alto: U32
  for +baixo: U32
  for -corpo: List<&2,U32>
  for +declarado: Nat
  for +antes: Nat
  for +cap: Nat
  for +recebido: Nat
  for medida_header: {B.nat64(declarado) == Some{B.Numero64{alto,baixo}} : Maybe<&2,B.Numero64>}
  for existente: {Nat.is_le(antes,declarado) == True{} : Bool}
  for real: {Nat.is_le(recebido,Nat.min(cap,Nat.sub(declarado,antes))) == True{} : Bool}
  for admitido: {Nat.is_le(declarado,R.limite_mensagem(S.limites(c))) == True{} : Bool}
  Leis.Regra2(I.LeuCorpo{antes,recebido,declarado},a,k,
    I.Atender{mundo,c,s,X.CorpoRecebido{alto,baixo,corpo}},t)
def read_confirmado_satisfaz_regra_original_para_qualquer_corpo(a,k,t,mundo,c,s,alto,baixo,corpo,declarado,antes,cap,recebido,medida_header,existente,real,admitido):
  Q.consumo_real_limitado_estabelece_regra2_original(a,k,t,mundo,c,s,
    X.CorpoRecebido{alto,baixo,corpo},declarado,antes,cap,recebido,
    Q.cabecalho_medido_estabelece_declaracao_original(alto,baixo,declarado,medida_header),
    existente,real,admitido)
