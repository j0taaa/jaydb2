import Base
import ../../../contrato/Requisitos.bend as R
import ../../../contrato/Logica.bend as L
import ../Certificado.bend as T
import ../Preparacao.bend as P

law falso:
  R.Valido(T.configuracao(), P.duplicado())
def falso():
  L.Ambos{{==}, L.Ambos{Unit{}, L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}}}
