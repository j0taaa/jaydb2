import Base
import ../../../contrato/Dados.bend as D
import ../../../contrato/Requisitos.bend as R
import ../Certificado.bend as T

law falso:
  R.Certifica(T.configuracao(), T.codigo(), T.programa(), T.contexto(), D.VTexto{"trocados"})
def falso(s, valido, identidade, n):
  T.certificado()(s, valido, identidade, n)
