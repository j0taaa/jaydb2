import Base
import ../../../contrato/Dados.bend as D
import ../../../contrato/Semantica.bend as S
import ../../../contrato/Requisitos.bend as R
import ../../../src/Nucleo.bend as N
import ../../../proof/Seguranca.bend as G
import ../Certificado.bend as T

law falso:
  R.SegurancaPercurso(N.percorrer(0n, N.iniciar(T.programa(), T.contexto(), T.argumentos(), T.inicial()), S.esquema(T.configuracao())),
    T.configuracao(), T.inicial(), T.contexto(), T.codigo(), T.argumentos())
def falso():
  G.certificado_cobre_execucao_autenticada(T.configuracao(), T.codigo(), T.programa(), T.contexto(), T.argumentos(),
    T.certificado(), T.inicial(), T.inicial_valido(), "credencial invalida", {==}, 0n)
