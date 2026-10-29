import Base
import ../../../contrato/Bytes.bend as B
import ../../../src/Transporte.bend as T
import ../../../proof/Transporte.bend as G

# A mesma prova nao pode apagar o segundo bloco recebido.
law falso:
  {T.separar([0, 0, 0, 0, 0, 0, 0, 1, 255, 7]) ==
    Some{T.Partes{[255], Nil{}}} : Maybe<&2, T.Partes>}
def falso():
  G.separar_inverte_toda_montagem_valida([255], [7],
    [0, 0, 0, 0, 0, 0, 0, 1, 255, 7], {==}, {==}, {==})
