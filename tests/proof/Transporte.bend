import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Logica.bend as L
import ../../src/Transporte.bend as T
import ../../proof/Transporte.bend as G

law todo_pacote_montado_separa_os_mesmos_blocos:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for -bs: List<&2, U32>
  for montado: {T.juntar(a, b) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for va: {B.octetos_validos(a) == True{} : Bool}
  for vb: {B.octetos_validos(b) == True{} : Bool}
  {T.separar(bs) == Some{T.Partes{a, b}} : Maybe<&2, T.Partes>}
def todo_pacote_montado_separa_os_mesmos_blocos(a, b, bs, montado, va, vb):
  G.separar_inverte_toda_montagem_valida(a, b, bs, montado, va, vb)

law todo_pacote_aceito_pode_ser_remontado_sem_mudar_um_octeto:
  for +bs: List<&2, U32>
  for +partes: T.Partes
  for aceito: {T.separar(bs) == Some{partes} : Maybe<&2, T.Partes>}
  G.SeparacaoExata(bs, partes)
def todo_pacote_aceito_pode_ser_remontado_sem_mudar_um_octeto(bs, partes, aceito):
  G.toda_separacao_aceita_reconstroi_pacote_original(bs, partes, aceito)
