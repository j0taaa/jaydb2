# Reaplicacao universal da fronteira que sera ligada ao hook nativo.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Logica.bend as L
import ../../src/Codec.bend as C
import ../../proof/AlocacoesComprimentos.bend as A

law campo_variavel_aberto_esta_dentro_dos_dois_limites:
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for variavel: A.Variavel(f)
  for abriu: {A.em_construcao(C.concluir_palavra(f, alto, baixo, pilha, corpo, teto)) == True{} : Bool}
  L.E<{C.menor_igual64(B.Numero64{alto, baixo}, corpo) == True{} : Bool},
    {C.menor_igual64(B.Numero64{alto, baixo}, teto) == True{} : Bool}>
def campo_variavel_aberto_esta_dentro_dos_dois_limites(f, alto, baixo, pilha, corpo, teto, variavel, abriu):
  A.abertura_variavel_real_respeita_corpo_e_teto(f, alto, baixo, pilha, corpo, teto, variavel, abriu)

law nenhuma_conferencia_insuficiente_abre_campo:
  for +c: C.Conferencia
  for +f: C.Finalidade
  for +q: B.Numero64
  for +pilha: C.Pilha
  for abriu: {A.em_construcao(C.abrir_conferido(c, f, q, pilha)) == True{} : Bool}
  {c == C.Cabe{} : C.Conferencia}
def nenhuma_conferencia_insuficiente_abre_campo(c, f, q, pilha, abriu):
  A.abertura_em_construcao_exige_conferencia_real(c, f, q, pilha, abriu)
