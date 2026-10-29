# Limites de cada read confirmado; nao fabrica eventos ou resultado POSIX.
import Base
import ../contrato/LAWS.bend as Leis
import ../contrato/Interface.bend as I
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Dados.bend as D
import ../contrato/Bytes.bend as B
import ./Ordens.bend as O
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F

law le_transitivo:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a,b) == True{} : Bool}
  for bc: {Nat.is_le(b,c) == True{} : Bool}
  {Nat.is_le(a,c) == True{} : Bool}
def le_transitivo(a,b,c,ab,bc):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+k:
      {==}
    case 1n+x 0n _:
      F.absurdo_booleano({Nat.is_le(1n+x,c) == True{} : Bool},ab)
    case 1n+x 1n+y 0n:
      F.absurdo_booleano({False{} == True{} : Bool},bc)
    case 1n+x 1n+y 1n+z:
      le_transitivo(x,y,z,ab,bc)

law minimo_nao_excede_restante:
  for +cap: Nat
  for +resto: Nat
  {Nat.is_le(Nat.min(cap,resto),resto) == True{} : Bool}
def minimo_nao_excede_restante(cap,resto):
  match cap resto:
    case _ 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+c 1n+r:
      minimo_nao_excede_restante(c,r)

law dentro_do_restante_nao_ultrapassa_declarado:
  for +declarado: Nat
  for +antes: Nat
  for +quantidade: Nat
  for existente: {Nat.is_le(antes,declarado) == True{} : Bool}
  for cabe: {Nat.is_le(quantidade,Nat.sub(declarado,antes)) == True{} : Bool}
  {Nat.is_le(Nat.add(antes,quantidade),declarado) == True{} : Bool}
def dentro_do_restante_nao_ultrapassa_declarado(declarado,antes,quantidade,existente,cabe):
  match declarado antes:
    case 0n 0n:
      cabe
    case 0n 1n+p:
      F.absurdo_booleano({Nat.is_le(Nat.add(1n+p,quantidade),0n) == True{} : Bool},existente)
    case 1n+d 0n:
      cabe
    case 1n+d 1n+a:
      dentro_do_restante_nao_ultrapassa_declarado(d,a,quantidade,existente,cabe)

law consumo_confirmado_respeita_declarado_e_limite:
  for +declarado: Nat
  for +antes: Nat
  for +cap: Nat
  for +recebido: Nat
  for +limite: Nat
  for existente: {Nat.is_le(antes,declarado) == True{} : Bool}
  for real: {Nat.is_le(recebido,Nat.min(cap,Nat.sub(declarado,antes))) == True{} : Bool}
  for admitido: {Nat.is_le(declarado,limite) == True{} : Bool}
  L.E<{Nat.is_le(Nat.add(antes,recebido),declarado) == True{} : Bool},
      {Nat.is_le(Nat.add(antes,recebido),limite) == True{} : Bool}>
def consumo_confirmado_respeita_declarado_e_limite(declarado,antes,cap,recebido,limite,existente,real,admitido):
  +dentro = dentro_do_restante_nao_ultrapassa_declarado(declarado,antes,recebido,existente,
    le_transitivo(recebido,Nat.min(cap,Nat.sub(declarado,antes)),Nat.sub(declarado,antes),
      real,minimo_nao_excede_restante(cap,Nat.sub(declarado,antes))))
  L.Ambos{dentro,le_transitivo(Nat.add(antes,recebido),declarado,limite,dentro,admitido)}

law cabecalho_medido_estabelece_declaracao_original:
  for +alto: U32
  for +baixo: U32
  for +declarado: Nat
  for medido: {B.nat64(declarado) == Some{B.Numero64{alto,baixo}} : Maybe<&2,B.Numero64>}
  {X.declarado_igual(alto,baixo,declarado) == True{} : Bool}
def cabecalho_medido_estabelece_declaracao_original(alto,baixo,declarado,medido):
  %Equal.sym(Maybe<&2,B.Numero64>,B.nat64(declarado),Some{B.Numero64{alto,baixo}},medido) :
    {X.declarado_igual_casos(alto,baixo,_) == True{} : Bool}
  F.e_booleano_intro(U32.is_eq(alto,alto),U32.is_eq(baixo,baixo),
    Equal.cong(Cmp,Bool,c => Cmp.is_eq(c),U32.cmp(alto,alto),EQ{},O.u32_refl(alto)),
    Equal.cong(Cmp,Bool,c => Cmp.is_eq(c),U32.cmp(baixo,baixo),EQ{},O.u32_refl(baixo)))

law consumo_real_limitado_estabelece_regra2_original:
  for -a: I.Ambiente
  for -k: String
  for -t: Nat
  for -mundo: Nat
  for c: S.Configuracao
  for -s: D.Estado
  for -entrada: X.Recepcao
  for +declarado: Nat
  for +antes: Nat
  for +cap: Nat
  for +recebido: Nat
  for declaracao: Leis.ComprimentoDeclarado(entrada,declarado)
  for existente: {Nat.is_le(antes,declarado) == True{} : Bool}
  for real: {Nat.is_le(recebido,Nat.min(cap,Nat.sub(declarado,antes))) == True{} : Bool}
  for admitido: {Nat.is_le(declarado,R.limite_mensagem(S.limites(c))) == True{} : Bool}
  Leis.Regra2(I.LeuCorpo{antes,recebido,declarado},a,k,I.Atender{mundo,c,s,entrada},t)
def consumo_real_limitado_estabelece_regra2_original(a,k,t,mundo,c,s,entrada,declarado,antes,cap,recebido,declaracao,existente,real,admitido):
  F.com_par(
    Leis.Regra2(I.LeuCorpo{antes,recebido,declarado},a,k,I.Atender{mundo,c,s,entrada},t),
    {Nat.is_le(Nat.add(antes,recebido),declarado) == True{} : Bool},
    {Nat.is_le(Nat.add(antes,recebido),R.limite_mensagem(S.limites(c))) == True{} : Bool},
    consumo_confirmado_respeita_declarado_e_limite(declarado,antes,cap,recebido,
      R.limite_mensagem(S.limites(c)),existente,real,admitido),
    declarado_cabe => limite_cabe => L.Ambos{declaracao,L.Ambos{declarado_cabe,limite_cabe}})
