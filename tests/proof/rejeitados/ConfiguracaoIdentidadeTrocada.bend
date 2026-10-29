import Base
import ../../../contrato/Semantica.bend as S
import ../../../contrato/Logica.bend as L
import ../../../contrato/Requisitos.bend as R
import ../../../src/Configuracao.bend as C
import ../../../proof/Configuracao.bend as P
import ../../../proof/Fundamentos.bend as F

# Mutacao: tentar trocar o nome do ambiente depois do teste real.
law falso:
  for c: S.Configuracao
  for +id: String
  for aceito: {C.valida(c, id) == True{} : Bool}
  {S.ambiente(c) == SCon{Chr{0}, id} : String}
def falso(c, id, aceito):
  F.com_par({S.ambiente(c) == SCon{Chr{0}, id} : String},
    {R.configuracao_valida(c) == True{} : Bool}, {S.ambiente(c) == id : String},
    P.aceita_exige_estrutura_e_identidade_exatas(c, id, aceito), estrutura => igual => igual)
