import Base
import ../../../contrato/Semantica.bend as S
import ../../../src/Nucleo.bend as N
import ../Certificado.bend as T

law falso:
  {N.percorrer(1n, N.iniciar(T.programa(), T.contexto(), T.argumentos(), T.inicial()), S.esquema(T.configuracao())) ==
    S.Prefixo{T.inicial(), Nil{}} : S.Percurso}
def falso():
  {==}
