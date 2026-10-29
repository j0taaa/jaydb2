import Base
import ../../../contrato/Semantica.bend as S
import ../../../contrato/Logica.bend as L
import ../Certificado.bend as T

law falso:
  S.Cumpre(T.configuracao(), S.Executando{T.inicial(), T.contexto(), T.codigo(), T.argumentos(), T.inicial(), Nil{}})
def falso():
  L.Ambos{{==}, L.Ambos{L.Esquerda{{==}}, Unit{}}}
