# Composicao das oito leis do protocolo gerado. As premissas abaixo sao
# contratos primitivos de fontes/ferramentas/IO, nunca LeiN ou RegraN.
# A ligacao desses contratos com Rust/Node/C permanece a fronteira confiavel
# explicita; nenhum contrato do compilador oficial e demonstrado aqui.
import Base
import ../contrato/Dados.bend as D
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ./FonteServico.bend as Fonte
import ./ModeloServico.bend as Modelo
import ./CenariosServico.bend as Cenarios
import ./HistoricoServico.bend as Historico
import ./Lei1Servico.bend as Uma
import ./Lei2Servico.bend as Duas
import ./Lei34Servico.bend as Admissao
import ./Lei5Servico.bend as Cinco
import ./Lei6Servico.bend as Seis
import ./Lei7Servico.bend as Sete
import ./Lei8Servico.bend as Oito
import ./PublicacaoServico.bend as Publicacao
import ./CanalServico.bend as Canal
import ./VisibilidadeServico.bend as Vis

# Cada familia e revelada em seu modulo: juizo inicial fechado; resultados
# das primitivas Codec/copia; execucao e historico certificados; efeitos de
# IO; retorno das primitivas sob Processavel externo, sem prazo fisico.
def Iniciais(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String) -> Type:
  @m: Nat -> Uma.OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), seed, c, pi, momento(m), m)
def Observacoes(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String) -> Type:
  @m: Nat -> Duas.OrigemDoModelo(base, c, seed, historico, momento, pi, m)
def FontesExecucao(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String) -> Type:
  @m: Nat -> Publicacao.OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m))
def IODoMomento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento) -> Type:
  match momento:
    case Cenarios.Inicializacao{}: Canal.FalhasReais(fonte, Fonte.cenario(fonte, mundo), Vis.quadros_inicial(fonte, c, seed(Unit{}), Fonte.inicial(fonte, mundo)))
    case Cenarios.Atendimento{+rx}: Sete.OrigemDaChamada7(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), rx, Fonte.chamada(fonte, mundo))

def Comunicacao(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String) -> Type:
  @m: Nat -> IODoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m))

def Premissas(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String) -> Type:
  L.E<Iniciais(base, c, seed, historico, momento, pi),
    L.E<Observacoes(base, c, seed, historico, momento, pi),
      L.E<FontesExecucao(base, c, seed, historico, momento, pi),
        L.E<Comunicacao(base, c, seed, historico, momento, pi),
          Oito.DisponibilidadeDoModelo(base, c, seed, historico, momento, pi)>>>>

# Projecoes lineares: cada prova consulta uma reabertura da mesma fonte.
def iniciais(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  p: Premissas(base, c, seed, historico, momento, pi)) -> Iniciais(base, c, seed, historico, momento, pi):
  match p:
    case L.Ambos{h, resto}: h

def observacoes(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  p: Premissas(base, c, seed, historico, momento, pi)) -> Observacoes(base, c, seed, historico, momento, pi):
  match p:
    case L.Ambos{inicial, L.Ambos{h, resto}}: h

def fontes_execucao(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  p: Premissas(base, c, seed, historico, momento, pi)) -> FontesExecucao(base, c, seed, historico, momento, pi):
  match p:
    case L.Ambos{inicial, L.Ambos{obs, L.Ambos{h, resto}}}: h

def io_do_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento,
  fonte_execucao: Publicacao.OrigemDoMomento(fonte, c, seed, historico, mundo, momento),
  io: IODoMomento(fonte, c, seed, historico, mundo, momento)) -> Sete.OrigemDoMomento7(fonte, c, seed, historico, mundo, momento):
  match momento:
    case Cenarios.Inicializacao{}: io
    case Cenarios.Atendimento{rx}:
      match fonte_execucao:
        case L.Ambos{real, juizo}: L.Ambos{real, io}

def comunicacao(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  p: Premissas(base, c, seed, historico, momento, pi)) ->
  @m: Nat -> Sete.OrigemDoMomento7(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m)):
  match p:
    case L.Ambos{inicial, L.Ambos{obs, L.Ambos{exec, L.Ambos{io, resto}}}}:
      +m => io_do_momento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m), exec(m), io(m))

def disponibilidade(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  p: Premissas(base, c, seed, historico, momento, pi)) -> Oito.DisponibilidadeDoModelo(base, c, seed, historico, momento, pi):
  match p:
    case L.Ambos{inicial, L.Ambos{obs, L.Ambos{exec, L.Ambos{io, h}}}}: h

# As Leis3/4/5 reutilizam a origem mais rica ja necessaria para a Lei6.
def admissao_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, +rx: X.Recepcao,
  dados: Fonte.ChamadaData, real: Cinco.ChamadaReal(fonte, c, s, rx, dados), juizo: Publicacao.JuizoDaChamada(fonte, c, rx, dados)) -> Admissao.OrigemChamada(fonte, c, s, rx, dados):
  match dados:
    case Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}: L.Ambos{real, juizo}

def admissao_do_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento,
  origem: Publicacao.OrigemDoMomento(fonte, c, seed, historico, mundo, momento)) -> Admissao.OrigemDoMomento(fonte, c, seed, historico, mundo, momento):
  match momento:
    case Cenarios.Inicializacao{}: Unit{}
    case Cenarios.Atendimento{+rx}:
      match origem:
        case L.Ambos{L.Ambos{cfg, L.Ambos{seed_valido, L.Ambos{historias, real}}}, juizo}:
          admissao_da_chamada(fonte, c, Historico.estado(historico(mundo), seed(Unit{})), rx, Fonte.chamada(fonte, mundo), real, juizo)

def execucao_do_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento,
  origem: Publicacao.OrigemDoMomento(fonte, c, seed, historico, mundo, momento)) -> Cinco.OrigemDoMomento(fonte, c, seed, historico, mundo, momento):
  match momento:
    case Cenarios.Inicializacao{}: Unit{}
    case Cenarios.Atendimento{rx}:
      match origem:
        case L.Ambos{real, juizo}: real

def admissoes(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  fontes: FontesExecucao(base, c, seed, historico, momento, pi)) ->
  @m: Nat -> Admissao.OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m)):
  +m => admissao_do_momento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m), fontes(m))

def execucoes(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  fontes: FontesExecucao(base, c, seed, historico, momento, pi)) ->
  @m: Nat -> Cinco.OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m)):
  +m => execucao_do_momento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m), fontes(m))

# ~reabrir denota uma declaracao FECHADA de fatos primitivos. Cada chamada
# fornece um valor fresco; programas e provas Type capturados nao sao copiados.
def Reabertas(-P: Type) -> Type:
  L.E<P, L.E<P, L.E<P, L.E<P, L.E<P, L.E<P, L.E<P, P>>>>>>>

def reabrir_fontes(~P: Type, ~reabrir: Unit -> P, -Q: Type, mesma: {P == Q : Type}) -> Reabertas(Q):
  %mesma : Reabertas(_)
  L.Ambos{reabrir(Unit{}), L.Ambos{reabrir(Unit{}), L.Ambos{reabrir(Unit{}), L.Ambos{reabrir(Unit{}), L.Ambos{reabrir(Unit{}), L.Ambos{reabrir(Unit{}), L.Ambos{reabrir(Unit{}), reabrir(Unit{})}}}}}}}

def compor(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  fontes: Reabertas(Premissas(base, c, seed, historico, momento, pi))) ->
  K.Contrato(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi))):
  match fontes:
    case L.Ambos{p1, L.Ambos{p2, L.Ambos{p3, L.Ambos{p4, L.Ambos{p5, L.Ambos{p6, L.Ambos{p7, p8}}}}}}}:
      L.Ambos{Uma.lei1_do_modelo(base, c, seed, historico, momento, pi, iniciais(base, c, seed, historico, momento, pi, p1)),
        L.Ambos{Duas.lei2_do_modelo(base, c, seed, historico, momento, pi, observacoes(base, c, seed, historico, momento, pi, p2)),
          L.Ambos{Admissao.lei3_do_modelo(base, c, seed, historico, momento, pi, admissoes(base, c, seed, historico, momento, pi, fontes_execucao(base, c, seed, historico, momento, pi, p3))),
            L.Ambos{Admissao.lei4_do_modelo(base, c, seed, historico, momento, pi, admissoes(base, c, seed, historico, momento, pi, fontes_execucao(base, c, seed, historico, momento, pi, p4))),
              L.Ambos{Cinco.lei5_do_modelo(base, c, seed, historico, momento, pi, execucoes(base, c, seed, historico, momento, pi, fontes_execucao(base, c, seed, historico, momento, pi, p5))),
                L.Ambos{Seis.lei6_do_modelo(base, c, seed, historico, momento, pi, fontes_execucao(base, c, seed, historico, momento, pi, p6)),
                  L.Ambos{Sete.lei7_do_modelo(base, c, seed, historico, momento, pi, comunicacao(base, c, seed, historico, momento, pi, p7)),
                    Oito.lei8_do_modelo(base, c, seed, historico, momento, pi, disponibilidade(base, c, seed, historico, momento, pi, p8))}}}}}}}

# O alvo e EXATAMENTE LAWS.Contrato: nao um registro menor renomeado.
law contrato_do_servico:
  for ~base: Fonte.Fonte
  for ~c: S.Configuracao
  for ~seed: Unit -> D.Estado
  for ~historico: Nat -> List<&2, Historico.Registro>
  for ~momento: Nat -> Cenarios.Momento
  for ~pi: String
  for ~P: Type
  for ~reabrir: Unit -> P
  for mesma: {P == Premissas(base, c, seed, historico, momento, pi) : Type}
  K.Contrato(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)))
def contrato_do_servico(base, c, seed, historico, momento, pi, P, reabrir, mesma):
  compor(base, c, seed, historico, momento, pi, reabrir_fontes(P, reabrir, Premissas(base, c, seed, historico, momento, pi), mesma))
