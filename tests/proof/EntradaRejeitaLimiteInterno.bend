# Regressao negativa: comprimento interno forjado nao justifica S.Limite.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./EntradaLimite.bend as F
law falso:
  {E.ler_mensagem(Some{B.Numero64{0, 32768}}, F.forjado(4), F.estado()) ==
    E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
def falso():
  {==}
