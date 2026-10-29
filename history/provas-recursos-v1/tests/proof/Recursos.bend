import Base
import ../../contrato/Recursos.bend as X
import ../../proof/Recursos.bend as R
import ./Certificado.bend as T

law igualdade_na_memoria_nao_e_excesso:
  {X.excedeu(T.configuracao(), X.Medicao{X.Memoria{}, 1n}) == False{} : Bool}
def igualdade_na_memoria_nao_e_excesso():
  R.memoria_igual_ao_teto_e_permitida(T.configuracao())

law byte_real_adicional_e_excesso:
  {X.excedeu(T.configuracao(), X.Medicao{X.Memoria{}, 2n}) == True{} : Bool}
def byte_real_adicional_e_excesso():
  {==}

law igualdade_no_tempo_e_expiracao:
  {X.excedeu(T.configuracao(), X.Medicao{X.Tempo{X.Preparar{}}, 1n}) == True{} : Bool}
def igualdade_no_tempo_e_expiracao():
  R.tempo_igual_ao_prazo_expirou(T.configuracao(), X.Preparar{})
