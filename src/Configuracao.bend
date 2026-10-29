# A configuracao deve nomear o ambiente realmente congelado pelo servidor.
# A identidade e um argumento do host, nunca um valor escolhido pelo cliente.
import Base
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R

def valida(c: S.Configuracao, identidade: String) -> Bool:
  S.Configuracao{e, ls, lim, +amb} = c
  R.configuracao_valida(S.Configuracao{e, ls, lim, amb}) && String.eq(amb, identidade)
