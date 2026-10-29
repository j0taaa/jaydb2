import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Livre.bend as L
import ./Terminacao.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificado(s, valido, identidade, n):
  L.percurso_livre_cobre_prefixos_e_final(
    S.executar(n, Client.programa(), C.esquema(), s, I.contexto(), I.argumentos()),
    C.esquema(), C.limites(), S.ambiente(I.config()), s, I.contexto(), B.codigo(), I.argumentos())

def B.termina(s, ctx, args):
  T.programa_finito(1n, Client.programa(), C.esquema(), s, ctx, args, Unit{})
