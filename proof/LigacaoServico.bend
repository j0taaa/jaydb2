# Ligacao dos marcos da unica rota com a observacao, compartilhada pelas leis.
import Base
import ../contrato/Logica.bend as L
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ./FonteServico.bend as Fonte
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as R
import ./Lei5Servico.bend as Cinco
import ./VisibilidadeServico.bend as Vis

def Marco(f: I.Fato) -> Type:
  match f:
    case I.ConfiguracaoEmUso{c}: Empty
    case I.EstadoVisivel{s}: Empty
    case _: Unit

def tipo_do_marco(-c: S.Configuracao, -p: S.Programa, -ini: Maybe<&2, D.Estado>,
  -xs: List<&2, Q.Quadro>, -t: Nat, f: I.Fato, marco: Marco(f)) ->
  {Q.observa_servico(c, p, ini, xs, t, f) == Q.observa(c, p, xs, t, f) : Type}:
  match f:
    case I.ConfiguracaoEmUso{c0}: L.ex_falso({Q.observa_servico(c, p, ini, xs, t, I.ConfiguracaoEmUso{c0}) == Q.observa(c, p, xs, t, I.ConfiguracaoEmUso{c0}) : Type}, marco)
    case I.EstadoVisivel{s}: L.ex_falso({Q.observa_servico(c, p, ini, xs, t, I.EstadoVisivel{s}) == Q.observa(c, p, xs, t, I.EstadoVisivel{s}) : Type}, marco)
    case I.InspecaoNaoModelada{a0}: {==}
    case I.EfeitoNaoModelado{a0}: {==}
    case I.InstanciaIniciou{a0}: {==}
    case I.InicializacaoRecusada{a0}: {==}
    case I.ProvaInicialAceita{}: {==}
    case I.Codificou{a0, a1}: {==}
    case I.Decodificou{a0, a1}: {==}
    case I.Guardou{a0, a1, a2}: {==}
    case I.Operou{a0, a1, a2, a3}: {==}
    case I.ConferiuComprimento{a0, a1}: {==}
    case I.AlocouCampo{a0, a1}: {==}
    case I.LeuCorpo{a0, a1, a2}: {==}
    case I.RecebeuRequisicao{a0}: {==}
    case I.Autenticou{a0, a1}: {==}
    case I.CertificadoAceito{a0, a1, a2}: {==}
    case I.CertificadoRejeitado{a0, a1}: {==}
    case I.ProgramaComecou{a0, a1, a2}: {==}
    case I.Avaliou{a0, a1, a2, a3}: {==}
    case I.Preparou{a0, a1}: {==}
    case I.Publicou{a0}: {==}
    case I.FalhouAmbiente{a0, a1, a2}: {==}
    case I.Concluiu{a0, a1, a2}: {==}
    case I.EntregouTudo{a0}: {==}
    case I.EntregaInterrompida{a0}: {==}
    case I.EncerrouCanal{}: {==}
    case I.ProximaChamada{a0, a1}: {==}

def observar_marco(-c: S.Configuracao, -p: S.Programa, -ini: Maybe<&2, D.Estado>,
  -xs: List<&2, Q.Quadro>, -t: Nat, f: I.Fato, marco: Marco(f), obs: Q.observa(c, p, xs, t, f)) ->
  Q.observa_servico(c, p, ini, xs, t, f):
  %Equal.sym(Type, Q.observa_servico(c, p, ini, xs, t, f), Q.observa(c, p, xs, t, f),
    tipo_do_marco(c, p, ini, xs, t, f, marco)) : _
  obs

def selecionar_marco(-c: S.Configuracao, -p: S.Programa, -ini: Maybe<&2, D.Estado>,
  -xs: List<&2, Q.Quadro>, -t: Nat, f: I.Fato, marco: Marco(f), obs: Q.observa_servico(c, p, ini, xs, t, f)) ->
  Q.observa(c, p, xs, t, f):
  %tipo_do_marco(c, p, ini, xs, t, f, marco) : _
  obs

def quadro_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData,
  +mundo: Nat, +t: Nat, +q: Q.Quadro, f: I.Fato,
  mesma: {dados == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData},
  consulta: {Q.consultar(Vis.quadros_chamada(c, s, recepcao, dados), t) == Some{q} : Maybe<&2, Q.Quadro>},
  relacao: Q.rel_fato(c, Cinco.programa_do_mundo(fonte, mundo), q, f), marco: Marco(f)) ->
  Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, dados), t, f):
  match dados:
    case Fonte.ChamadaData{cf, +pf, cert, termina, +estado, +ferramentas, +micro}:
      observar_marco(c, Fonte.programa(fonte, pf), Some{s},
        R.gerar(c, recepcao, estado, s, ferramentas, micro), t, f, marco,
        Q.consulta_estabelece_observacao(c, Fonte.programa(fonte, pf),
        R.gerar(c, recepcao, estado, s, ferramentas, micro), t, q, f, consulta,
        (%Equal.sym(S.Programa, Fonte.programa(fonte, pf), Cinco.programa_do_mundo(fonte, mundo),
            Cinco.mesma_raiz_da_chamada(fonte, mundo,
              Fonte.ChamadaData{cf, pf, cert, termina, estado, ferramentas, micro}, mesma)) :
          Q.rel_fato(c, _, q, f) relacao)))

# O mesmo produtor de fatos, com a guarda do cenario aberta uma unica vez.
def introduzir_quadro(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +recepcao: X.Recepcao, +t: Nat, +q: Q.Quadro, f: I.Fato,
  canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  consulta: {Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{q} : Maybe<&2, Q.Quadro>},
  relacao: Q.rel_fato(c, Cinco.programa_do_mundo(fonte, mundo), q, f), marco: Marco(f)) ->
  I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, f):
  Fonte.introduzir_fato(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, f, {==},
    Fonte.origem_canonica(fonte, I.Atender{mundo, c, s, recepcao}, Fonte.cenario(fonte, mundo), t, f, canonico,
      quadro_da_chamada(fonte, c, s, recepcao, Fonte.chamada(fonte, mundo), mundo, t, q, f, {==}, consulta, relacao, marco)))


def quadro_da_observacao(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData, +t: Nat,
  f: I.Fato, marco: Marco(f),
  obs: Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, dados), t, f)) ->
  {Q.consultar(Vis.quadros_chamada(c, s, recepcao, dados), t) == Some{Q.quadro_do_fato(f)} : Maybe<&2, Q.Quadro>}:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, +estado, +ferramentas, +micro}:
      Q.observacao_quadro(c, Fonte.programa(fonte, pf), R.gerar(c, recepcao, estado, s, ferramentas, micro), t, f,
        selecionar_marco(c, Fonte.programa(fonte, pf), Some{s}, R.gerar(c, recepcao, estado, s, ferramentas, micro), t, f, marco, obs))

def quadro_por_guardas(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, +t: Nat, f: I.Fato, marco: Marco(f),
  entrada: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
      Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, f)>>) ->
  {Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) ==
    Some{Q.quadro_do_fato(f)} : Maybe<&2, Q.Quadro>}:
  match entrada:
    case L.Ambos{nome, L.Ambos{canonico, obs}}:
      quadro_da_observacao(fonte, c, s, recepcao, Fonte.chamada(fonte, mundo), t, f, marco, obs)

def extrair_quadro(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +recepcao: X.Recepcao, +t: Nat, f: I.Fato, marco: Marco(f),
  obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, f)) ->
  {Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) ==
    Some{Q.quadro_do_fato(f)} : Maybe<&2, Q.Quadro>}:
  quadro_por_guardas(fonte, c, mundo, s, recepcao, t, f, marco,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, f, obs))

# Associatividade da mesma lista nao muda os fatos; nenhuma funcao de host e assumida aqui.
def introduzir_na_lista(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +recepcao: X.Recepcao, +xs: List<&2, Q.Quadro>, +t: Nat, +q: Q.Quadro,
  f: I.Fato, canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  mesma: {Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)) == xs : List<&2, Q.Quadro>},
  consulta: {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>},
  relacao: Q.rel_fato(c, Cinco.programa_do_mundo(fonte, mundo), q, f), marco: Marco(f)) ->
  I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, f):
  introduzir_quadro(fonte, c, mundo, s, recepcao, t, q, f, canonico,
    (%Equal.sym(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), xs, mesma) :
      {Q.consultar(_, t) == Some{q} : Maybe<&2, Q.Quadro>} consulta), relacao, marco)

def extrair_na_lista(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +recepcao: X.Recepcao, +xs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato,
  mesma: {Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)) == xs : List<&2, Q.Quadro>},
  marco: Marco(f), obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, f)) ->
  {Q.consultar(xs, t) == Some{Q.quadro_do_fato(f)} : Maybe<&2, Q.Quadro>}:
  %mesma : {Q.consultar(_, t) == Some{Q.quadro_do_fato(f)} : Maybe<&2, Q.Quadro>}
  extrair_quadro(fonte, c, mundo, s, recepcao, t, f, marco, obs)

# Projecoes de dados; a rota e exatamente a que Fonte ja observou.
def micro_dos_dados(dados: Fonte.ChamadaData) -> R.Micro:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, be, ferramentas, micro}: micro

def caso_dos_dados(~c: S.Configuracao, recepcao: X.Recepcao, dados: Fonte.ChamadaData) -> R.Caso:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, be, ferramentas, micro}: R.decidir(c, recepcao, be, ferramentas)

law quadros_seguem_o_caso:
  for ~c: S.Configuracao
  for +s: D.Estado
  for +recepcao: X.Recepcao
  for +dados: Fonte.ChamadaData
  {Vis.quadros_chamada(c, s, recepcao, dados) ==
    R.render(micro_dos_dados(dados), s, caso_dos_dados(c, recepcao, dados)) : List<&2, Q.Quadro>}
def quadros_seguem_o_caso(c, s, recepcao, dados):
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, be, ferramentas, micro}: {==}
