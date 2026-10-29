# Consequencias do contrato, com provas completas em Bend.
# Receber `c: Contrato(a,k)` nao demonstra esse contrato: estes teoremas
# dizem o que se pode concluir DEPOIS de ele ter sido provado para k.
import Base
import ./Logica.bend as L
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Interface.bend as I
import ./LAWS.bend as Leis

def obter_lei5(-a: I.Ambiente, -k: String, c: Leis.Contrato(a, k)) -> Leis.Lei5(a, k):
  match c:
    case L.Ambos{l1, L.Ambos{l2, L.Ambos{l3, L.Ambos{l4, L.Ambos{l5, resto}}}}}:
      l5

def obter_lei6(-a: I.Ambiente, -k: String, c: Leis.Contrato(a, k)) -> Leis.Lei6(a, k):
  match c:
    case L.Ambos{l1, L.Ambos{l2, L.Ambos{l3, L.Ambos{l4, L.Ambos{l5, L.Ambos{l6, resto}}}}}}:
      l6

law inspecao_fora_do_modelo_impossivel:
  for -a: I.Ambiente
  for -k: String
  for contrato: Leis.Contrato(a, k)
  for x: I.Cenario
  for t: Nat
  for descricao: String
  for ocorreu: I.Acontece(a, k, x, t, I.InspecaoNaoModelada{descricao})
  Empty

def inspecao_fora_do_modelo_impossivel(a, k, contrato, x, t, descricao, ocorreu):
  obter_lei5(a, k, contrato)(x, t, I.InspecaoNaoModelada{descricao}, ocorreu)

def validade_da_publicacao(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -t: Nat, -s: D.Estado, regra: Leis.Regra6(I.Publicou{s}, a, k, x, t)) -> R.Valido(I.configuracao(x), s):
  match regra:
    case L.Ambos{valido, resto}:
      valido

law toda_publicacao_e_valida:
  for -a: I.Ambiente
  for -k: String
  for contrato: Leis.Contrato(a, k)
  for x: I.Cenario
  for t: Nat
  for estado: D.Estado
  for ocorreu: I.Acontece(a, k, x, t, I.Publicou{estado})
  R.Valido(I.configuracao(x), estado)

def toda_publicacao_e_valida(a, k, contrato, x, t, estado, ocorreu):
  validade_da_publicacao(a, k, x, t, estado,
    obter_lei6(a, k, contrato)(x, t, I.Publicou{estado}, ocorreu))

law recusa_nativa_conserva_estado:
  for -a: I.Ambiente
  for -k: String
  for contrato: Leis.Contrato(a, k)
  for x: I.Cenario
  for t: Nat
  for valor: D.Valor
  for publicado: D.Estado
  for fecha: Bool
  for ocorreu: I.Acontece(a, k, x, t, I.Concluiu{S.Resposta{S.Recusa{}, valor}, publicado, fecha})
  L.E<{publicado == I.inicial(x) : D.Estado}, Leis.NenhumaPublicacao(a, k, x)>

def recusa_nativa_conserva_estado(a, k, contrato, x, t, valor, publicado, fecha, ocorreu):
  obter_lei6(a, k, contrato)(x, t, I.Concluiu{S.Resposta{S.Recusa{}, valor}, publicado, fecha}, ocorreu)

law erro_nao_apaga_eventos:
  for -e: D.Esquema
  for -s: D.Estado
  for -ts: List<&2, S.Evento>
  for -o: D.Operacao
  {S.continuar_percurso(0n, S.OperacaoFalhou{s, S.Evento{o, S.ErroDeDados{}}}, e, ts) ==
    S.Final{s, S.acrescentar(ts, S.Evento{o, S.ErroDeDados{}}),
      S.Resposta{S.Dados{}, D.VAusente{}}} : S.Percurso}

def erro_nao_apaga_eventos(e, s, ts, o):
  {==}
