# Ligacao do teste executado na inicializacao a relacao original.
# Nao define Ambiente, observa, Processavel ou qualquer fato do host.
import Base
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../src/Configuracao.bend as C
import ./Fundamentos.bend as F
import ./Ordens.bend as O

law aceita_exige_estrutura_e_identidade_exatas:
  for c: S.Configuracao
  for +identidade: String
  for aceito: {C.valida(c, identidade) == True{} : Bool}
  L.E<{R.configuracao_valida(c) == True{} : Bool},
    {S.ambiente(c) == identidade : String}>
def aceita_exige_estrutura_e_identidade_exatas(c, identidade, aceito):
  match c:
    case S.Configuracao{e, ls, lim, +amb}:
      F.com_par(
        L.E<{R.configuracao_valida(S.Configuracao{e, ls, lim, amb}) == True{} : Bool}, {amb == identidade : String}>,
        {R.configuracao_valida(S.Configuracao{e, ls, lim, amb}) == True{} : Bool},
        {String.eq(amb, identidade) == True{} : Bool},
        F.e_booleano_separar(R.configuracao_valida(S.Configuracao{e, ls, lim, amb}), String.eq(amb, identidade), aceito),
        estrutura => igual => L.Ambos{estrutura, O.string_igual(amb, identidade, igual)})

law aceita_satisfaz_configuracao_valida_original:
  for a: I.Ambiente
  for c: S.Configuracao
  for aceito: {C.valida(c, I.identidade(a)) == True{} : Bool}
  I.ConfiguracaoValida(a, c)
def aceita_satisfaz_configuracao_valida_original(a, c, aceito):
  aceita_exige_estrutura_e_identidade_exatas(c, I.identidade(a), aceito)

law configuracao_original_valida_e_aceita:
  for a: I.Ambiente
  for c: S.Configuracao
  for valida: I.ConfiguracaoValida(a, c)
  {C.valida(c, I.identidade(a)) == True{} : Bool}
def configuracao_original_valida_e_aceita(a, c, valida):
  match c:
    case S.Configuracao{+e, ls, +lim, +amb}:
      +id = I.identidade(a)
      F.com_par({C.valida(S.Configuracao{e, ls, lim, amb}, id) == True{} : Bool},
        {R.configuracao_valida(S.Configuracao{e, ls, lim, amb}) == True{} : Bool}, {amb == id : String}, valida,
        estrutura => igual => F.e_booleano_intro(R.configuracao_valida(S.Configuracao{e, ls, lim, amb}), String.eq(amb, id),
          estrutura, (%Equal.sym(String, amb, id, igual) :
            {String.eq(_, id) == True{} : Bool}
            O.string_eq_refl(id))))
