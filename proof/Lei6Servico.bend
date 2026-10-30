# Publicacao do mesmo resultado Bend e visibilidade do host serial.
import Base
import ./PublicacaoServico.bend as PublicacaoServico
import ./RefinamentoServico.bend as Ref
import ../src/Configuracao.bend as Config
import ./LigacaoServico.bend as Ligacao
import ./FechosServico.bend as Fechos
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ../src/Nucleo.bend as N
import ./FonteServico.bend as Fonte
import ./RotasServico.bend as R
import ./ProtocoloServico.bend as Q
import ./VisibilidadeServico.bend as Vis
import ./FasesServico.bend as Fases
import ./ConclusaoServico.bend as Conclusao
import ./Lei5Servico.bend as Cinco
import ./Publicacao.bend as U
import ./Fundamentos.bend as F
import ./Chamada.bend as Chamada
import ./CenariosServico.bend as Cenarios
import ./HistoricoServico.bend as Historico
import ./ModeloServico.bend as Modelo

# A proxima iteracao herda a conclusao anterior; entrega nao refaz o store.
def OrigemSeguinte(-xs: List<&2, Q.Quadro>, -t: Nat, -a: D.Estado, -b: D.Estado) -> Type:
  L.E<{b == a : D.Estado},
    &r: S.Resposta -> &fecha: Bool -> &u: Nat ->
      L.E<{Nat.is_lt(u, t) == True{} : Bool},
        {Q.consultar(xs, u) == Some{Q.Concluida{r, a, fecha}} : Maybe<&2, Q.Quadro>}>>

def primeiro_seguinte(q: Q.Quadro) -> Maybe<&2, D.Estado>:
  match q:
    case Q.Seguinte{a, b}: Some{a}
    case _: None{}

def segundo_seguinte(q: Q.Quadro) -> Maybe<&2, D.Estado>:
  match q:
    case Q.Seguinte{a, b}: Some{b}
    case _: None{}

def estados_da_sucessao(+s: D.Estado, +a: D.Estado, +b: D.Estado,
  igualdade: {Q.Seguinte{s, s} == Q.Seguinte{a, b} : Q.Quadro}) ->
  L.E<{a == s : D.Estado}, {b == a : D.Estado}>:
  F.com_par(L.E<{a == s : D.Estado}, {b == a : D.Estado}>,
    {Q.Seguinte{s, s} == Q.Seguinte{a, b} : Q.Quadro},
    {Q.Seguinte{s, s} == Q.Seguinte{a, b} : Q.Quadro},
    Chamada.duplicar_igualdade(Q.Quadro, Q.Seguinte{s, s}, Q.Seguinte{a, b}, igualdade),
    primeiro => segundo =>
      F.com_par(L.E<{a == s : D.Estado}, {b == a : D.Estado}>,
        {a == s : D.Estado}, {a == s : D.Estado},
        Chamada.duplicar_igualdade(D.Estado, a, s,
          Equal.sym(D.Estado, s, a, F.algum_injetivo(D.Estado, s, a,
            Equal.cong(Q.Quadro, Maybe<&2, D.Estado>, primeiro_seguinte,
              Q.Seguinte{s, s}, Q.Seguinte{a, b}, primeiro)))),
        inicial => copia => L.Ambos{inicial,
          Equal.trans(D.Estado, b, s, a,
            Equal.sym(D.Estado, s, b, F.algum_injetivo(D.Estado, s, b,
              Equal.cong(Q.Quadro, Maybe<&2, D.Estado>, segundo_seguinte,
                Q.Seguinte{s, s}, Q.Seguinte{a, b}, segundo))),
            Equal.sym(D.Estado, a, s, copia))}))

def sucessao_local_presente(+s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, t: Nat,
  +a: D.Estado, +b: D.Estado,
  presente: {Q.consultar([Q.Concluida{r, s, False{}}, Q.Entregue{bs}, Q.Seguinte{s, s}], t) ==
    Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}) ->
  OrigemSeguinte([Q.Concluida{r, s, False{}}, Q.Entregue{bs}, Q.Seguinte{s, s}], t, a, b):
  match t:
    case 0n:
      L.ex_falso(OrigemSeguinte([Q.Concluida{r, s, False{}}, Q.Entregue{bs}, Q.Seguinte{s, s}], 0n, a, b),
        Fechos.sem_seguinte_na_frente(Q.Concluida{r, s, False{}}, Nil{}, a, b, {==}, Fechos.sem_seguinte_vazio(a, b))(0n, presente))
    case 1n+k:
      match k:
        case 0n:
          L.ex_falso(OrigemSeguinte([Q.Concluida{r, s, False{}}, Q.Entregue{bs}, Q.Seguinte{s, s}], 1n, a, b),
            Fechos.sem_seguinte_na_frente(Q.Entregue{bs}, Nil{}, a, b, {==}, Fechos.sem_seguinte_vazio(a, b))(0n, presente))
        case 1n+j:
          match j:
            case 0n:
              F.com_par(OrigemSeguinte([Q.Concluida{r, s, False{}}, Q.Entregue{bs}, Q.Seguinte{s, s}], 2n, a, b),
                {a == s : D.Estado}, {b == a : D.Estado},
                estados_da_sucessao(s, a, b, F.algum_injetivo(Q.Quadro, Q.Seguinte{s, s}, Q.Seguinte{a, b}, presente)),
                mesmo => conserva => L.Ambos{conserva, (r, False{}, 0n, L.Ambos{{==},
                  (%Equal.sym(D.Estado, a, s, mesmo) :
                    {Some{Q.Concluida{r, s, False{}}} == Some{Q.Concluida{r, _, False{}}} : Maybe<&2, Q.Quadro>} {==})})})
            case 1n+n:
              L.ex_falso(OrigemSeguinte([Q.Concluida{r, s, False{}}, Q.Entregue{bs}, Q.Seguinte{s, s}], 3n+n, a, b),
                F.nenhum_nao_algum(Q.Quadro, Q.Seguinte{a, b}, presente))

# Sem outro marco Seguinte no prefixo, sua origem permanece a mesma ao deslocar.
def levantar_origem_seguinte(+antes: List<&2, Q.Quadro>, +resto: List<&2, Q.Quadro>,
  -t: Nat, +i: Nat, -a: D.Estado, -b: D.Estado,
  posicao: {t == Nat.add(Q.tamanho(antes), i) : Nat},
  origem: OrigemSeguinte(resto, i, a, b)) ->
  OrigemSeguinte(Q.concatenar(antes, resto), t, a, b):
  match origem:
    case L.Ambos{conserva, (r, fecha, +u, L.Ambos{menor, consulta})}:
      L.Ambos{conserva, (r, fecha, Nat.add(Q.tamanho(antes), u), L.Ambos{
        (%Equal.sym(Nat, t, Nat.add(Q.tamanho(antes), i), posicao) :
          {Nat.is_lt(Nat.add(Q.tamanho(antes), u), _) == True{} : Bool}
          Q.ordem_deslocada(Q.tamanho(antes), u, i, menor)),
        Equal.trans(Maybe<&2, Q.Quadro>,
          Q.consultar(Q.concatenar(antes, resto), Nat.add(Q.tamanho(antes), u)),
          Q.consultar(resto, u), Some{Q.Concluida{r, a, fecha}},
          Q.consultar_apos_prefixo(antes, resto, u), consulta)})}

# Apenas duas possibilidades de N.concluir: sucesso com store anterior ou rollback.
def fim_nao_publica(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +entrega: R.Entrega,
  sem: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool},
  conserva: {U.status_sucesso(r) == False{} : Bool} -> {s == I.inicial(x) : D.Estado},
  status: {U.status_sucesso(r) == False{} : Bool},
  extrair: @u: Nat -> @w: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w}) ->
    {Q.consultar(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) ->
  L.E<{s == I.inicial(x) : D.Estado}, K.NenhumaPublicacao(a, k, x)>:
  F.com_par(L.E<{s == I.inicial(x) : D.Estado}, K.NenhumaPublicacao(a, k, x)>,
    {U.status_sucesso(r) == False{} : Bool}, {U.status_sucesso(r) == False{} : Bool},
    Chamada.duplicar_igualdade(Bool, U.status_sucesso(r), False{}, status),
    anterior => nenhuma => L.Ambos{conserva(anterior),
      Fases.nenhuma_publicacao_real(a, k, x, Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)),
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega),
          sem, Fases.resposta_nao_publica(s, r, bs, fecha, entrega, nenhuma)), extrair)})

def atomica_do_fecho(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +entrega: R.Entrega,
  sem: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool},
  conserva: {U.status_sucesso(r) == False{} : Bool} -> {s == I.inicial(x) : D.Estado},
  introduzir: @u: Nat -> @w: D.Estado ->
    {Q.consultar(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Publicou{w}),
  extrair: @u: Nat -> @w: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w}) ->
    {Q.consultar(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) ->
  K.ConclusaoAtomica(r, a, k, x, Nat.add(Q.tamanho(antes), Conclusao.local_conclusao(s, r, bs)), s):
  match r:
    case S.Resposta{S.Sucesso{}, +v}:
      (Nat.add(Q.tamanho(antes), 1n), L.Ambos{Q.ordem_deslocada(Q.tamanho(antes), 1n, 2n, {==}),
        introduzir(Nat.add(Q.tamanho(antes), 1n), s,
          Q.consultar_apos_prefixo(antes, R.render_conclusao(N.Conclusao{s, S.Resposta{S.Sucesso{}, v}, bs}, fecha, entrega), 1n))})
    case S.Resposta{S.Recusa{}, v}: fim_nao_publica(a, k, x, antes, s, S.Resposta{S.Recusa{}, v}, bs, fecha, entrega, sem, conserva, {==}, extrair)
    case S.Resposta{S.Entrada{}, v}: fim_nao_publica(a, k, x, antes, s, S.Resposta{S.Entrada{}, v}, bs, fecha, entrega, sem, conserva, {==}, extrair)
    case S.Resposta{S.Autenticacao{}, v}: fim_nao_publica(a, k, x, antes, s, S.Resposta{S.Autenticacao{}, v}, bs, fecha, entrega, sem, conserva, {==}, extrair)
    case S.Resposta{S.Certificado{}, v}: fim_nao_publica(a, k, x, antes, s, S.Resposta{S.Certificado{}, v}, bs, fecha, entrega, sem, conserva, {==}, extrair)
    case S.Resposta{S.Dados{}, v}: fim_nao_publica(a, k, x, antes, s, S.Resposta{S.Dados{}, v}, bs, fecha, entrega, sem, conserva, {==}, extrair)
    case S.Resposta{S.Limite{}, v}: fim_nao_publica(a, k, x, antes, s, S.Resposta{S.Limite{}, v}, bs, fecha, entrega, sem, conserva, {==}, extrair)
    case S.Resposta{S.Falha{}, v}: fim_nao_publica(a, k, x, antes, s, S.Resposta{S.Falha{}, v}, bs, fecha, entrega, sem, conserva, {==}, extrair)

def transportar_conclusao6(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool,
  -t: Nat, +q: Q.Quadro,
  igual: L.E<{t == Nat.add(Q.tamanho(antes), Conclusao.local_conclusao(s, r, bs)) : Nat},
    {q == Q.Concluida{r, s, fecho} : Q.Quadro}>,
  atomica: K.ConclusaoAtomica(r, a, k, x, Nat.add(Q.tamanho(antes), Conclusao.local_conclusao(s, r, bs)), s)) ->
  K.Regra6(Conclusao.fato_da_conclusao(q), a, k, x, t):
  match igual:
    case L.Ambos{pos, campos}:
      %Equal.sym(Nat, t, Nat.add(Q.tamanho(antes), Conclusao.local_conclusao(s, r, bs)), pos) :
        K.Regra6(Conclusao.fato_da_conclusao(q), a, k, x, _)
      %Equal.sym(Q.Quadro, q, Q.Concluida{r, s, fecho}, campos) :
        K.Regra6(Conclusao.fato_da_conclusao(_), a, k, x, Nat.add(Q.tamanho(antes), Conclusao.local_conclusao(s, r, bs)))
      atomica

law conclusao_do_fecho_obedece_regra6:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecho: Bool
  for +entrega: R.Entrega
  for +t: Nat
  for +r2: S.Resposta
  for +s2: D.Estado
  for +f2: Bool
  for sem_publicar: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool}
  for sem_concluir: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool}
  for conserva: {U.status_sucesso(r) == False{} : Bool} -> {s == I.inicial(x) : D.Estado}
  for consulta: {Q.consultar(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), t) == Some{Q.Concluida{r2, s2, f2}} : Maybe<&2, Q.Quadro>}
  for introduzir: @u: Nat -> @w: D.Estado ->
    {Q.consultar(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Publicou{w})
  for extrair: @u: Nat -> @w: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w}) ->
    {Q.consultar(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  K.Regra6(I.Concluiu{r2, s2, f2}, a, k, x, t)
def conclusao_do_fecho_obedece_regra6(a, k, x, antes, s, r, bs, fecho, entrega, t, r2, s2, f2,
  sem_publicar, sem_concluir, conserva, consulta, introduzir, extrair):
  transportar_conclusao6(a, k, x, antes, s, r, bs, fecho, t, Q.Concluida{r2, s2, f2},
    Conclusao.conclusao_localizada_no_fecho(antes, s, r, bs, fecho, entrega, t, Q.Concluida{r2, s2, f2}, sem_concluir, {==}, consulta),
    atomica_do_fecho(a, k, x, antes, s, r, bs, fecho, entrega, sem_publicar, conserva, introduzir, extrair))

# Os tres usos da igualdade reordenam a MESMA lista, sem novo observador.
def conclusao_conforme_fecho(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +inicial: D.Estado, +recepcao: X.Recepcao,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +entrega: R.Entrega,
  +t: Nat, +r2: S.Resposta, +s2: D.Estado, +f2: Bool,
  canonico: {I.Atender{mundo, c, inicial, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  mesma: {Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)) ==
    Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)) : List<&2, Q.Quadro>},
  pub: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool},
  concl: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool},
  conserva: {U.status_sucesso(r) == False{} : Bool} -> {s == inicial : D.Estado},
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)), t) ==
    Some{Q.Concluida{r2, s2, f2}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Concluiu{r2, s2, f2}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao}, t):
  Cinco.com_quatro(
    {Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)) ==
      Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)) : List<&2, Q.Quadro>},
    K.Regra6(I.Concluiu{r2, s2, f2}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao}, t),
    Cinco.quatro_igualdades(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)),
      Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), mesma),
    atual => introduzir => extrair => sobra =>
      conclusao_do_fecho_obedece_regra6(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao},
        antes, s, r, bs, fecho, entrega, t, r2, s2, f2, pub, concl, conserva,
        (%atual : {Q.consultar(_, t) == Some{Q.Concluida{r2, s2, f2}} : Maybe<&2, Q.Quadro>} consulta),
        +u => +w => presente => Ligacao.introduzir_na_lista(fonte, c, mundo, inicial, recepcao,
          Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u, Q.Publicada{w}, I.Publicou{w},
          canonico, introduzir, presente, {==}, Unit{}),
        +u => +w => fato => Ligacao.extrair_na_lista(fonte, c, mundo, inicial, recepcao,
          Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u, I.Publicou{w}, extrair, Unit{}, fato)))

def consumir_fecho_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +inicial: D.Estado, +recepcao: X.Recepcao, +xs: List<&2, Q.Quadro>, +caso: R.Caso,
  +t: Nat, +r: S.Resposta, +s: D.Estado, +fecha: Bool,
  canonico: {I.Atender{mundo, c, inicial, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  mesma: {Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)) == xs : List<&2, Q.Quadro>},
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Concluida{r, s, fecha}} : Maybe<&2, Q.Quadro>},
  resultado: &h: Fechos.Fecho -> L.E<Fechos.Forma(xs, caso, Some{h}), Fechos.EstadoDoFecho(inicial, Some{h})>) ->
  K.Regra6(I.Concluiu{r, s, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao}, t):
  match resultado:
    case (Fechos.Fecho{antes, N.Conclusao{w, rp, bs}, fecho, entrega, origem},
      L.Ambos{L.Ambos{mesmo_caso, L.Ambos{traco, L.Ambos{pub, concl}}}, estado}):
      conclusao_conforme_fecho(fonte, c, mundo, inicial, recepcao, antes, w, rp, bs, fecho, entrega, t, r, s, fecha,
        canonico, Equal.trans(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)), xs,
          Q.concatenar(antes, R.render_conclusao(N.Conclusao{w, rp, bs}, fecho, entrega)), mesma, traco), pub, concl, estado, consulta)

def conclusao_por_guardas(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, +t: Nat, +r: S.Resposta, +w: D.Estado, +fecha: Bool,
  entrada: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
      Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, I.Concluiu{r, w, fecha})>>) ->
  K.Regra6(I.Concluiu{r, w, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match entrada:
    case L.Ambos{nome, L.Ambos{canonico, observado}}:
      F.com_par(K.Regra6(I.Concluiu{r, w, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        {Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Concluida{r, w, fecha}} : Maybe<&2, Q.Quadro>},
        {Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Concluida{r, w, fecha}} : Maybe<&2, Q.Quadro>},
        Chamada.duplicar_igualdade(Maybe<&2, Q.Quadro>, Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t), Some{Q.Concluida{r, w, fecha}},
          Ligacao.quadro_da_observacao(fonte, c, s, recepcao, Fonte.chamada(fonte, mundo), t, I.Concluiu{r, w, fecha}, Unit{}, observado)),
        busca => consulta => consumir_fecho_da_chamada(fonte, c, mundo, s, recepcao,
          R.render(Ligacao.micro_dos_dados(Fonte.chamada(fonte, mundo)), s, Ligacao.caso_dos_dados(c, recepcao, Fonte.chamada(fonte, mundo))),
          Ligacao.caso_dos_dados(c, recepcao, Fonte.chamada(fonte, mundo)), t, r, w, fecha, canonico,
          Ligacao.quadros_seguem_o_caso(c, s, recepcao, Fonte.chamada(fonte, mundo)), consulta,
          Fechos.inverter_conclusao_com_estado(Ligacao.micro_dos_dados(Fonte.chamada(fonte, mundo)), s,
            Ligacao.caso_dos_dados(c, recepcao, Fonte.chamada(fonte, mundo)), t, r, w, fecha,
            (%Ligacao.quadros_seguem_o_caso(c, s, recepcao, Fonte.chamada(fonte, mundo)) :
              {Q.consultar(_, t) == Some{Q.Concluida{r, w, fecha}} : Maybe<&2, Q.Quadro>} busca))))

law conclusao_da_fonte_obedece_regra6:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +recepcao: X.Recepcao
  for +t: Nat
  for +r: S.Resposta
  for +w: D.Estado
  for +fecha: Bool
  for observado: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.Concluiu{r, w, fecha})
  K.Regra6(I.Concluiu{r, w, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t)
def conclusao_da_fonte_obedece_regra6(fonte, c, mundo, s, recepcao, t, r, w, fecha, observado):
  conclusao_por_guardas(fonte, c, mundo, s, recepcao, t, r, w, fecha,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.Concluiu{r, w, fecha}, observado))

def negar_seguinte(-xs: List<&2, Q.Quadro>, +t: Nat, +a: D.Estado, +b: D.Estado,
  sem: Fechos.SemSeguinte(xs), consulta: {Q.consultar(xs, t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}) -> OrigemSeguinte(xs, t, a, b):
  L.ex_falso(OrigemSeguinte(xs, t, a, b), sem(a, b, t, consulta))

def sucessao_completa(+s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool,
  +proxima: Bool, +t: Nat, +a: D.Estado, +b: D.Estado,
  consulta: {Q.consultar(Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, R.Completa{proxima})}, t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}) ->
  OrigemSeguinte(Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, R.Completa{proxima})}, t, a, b):
  match fecha:
    case True{}:
      negar_seguinte([Q.Concluida{r, s, True{}}, Q.Entregue{bs}, Q.Fechada{}], t, a, b,
        Fechos.prefixar_sem_seguinte(Q.Concluida{r, s, True{}}, [Q.Entregue{bs}, Q.Fechada{}], {==},
          Fechos.prefixar_sem_seguinte(Q.Entregue{bs}, [Q.Fechada{}], {==},
            Fechos.prefixar_sem_seguinte(Q.Fechada{}, Nil{}, {==}, Fechos.vazio_sem_seguinte()))), consulta)
    case False{}:
      match proxima:
        case False{}:
          negar_seguinte([Q.Concluida{r, s, False{}}, Q.Entregue{bs}], t, a, b,
            Fechos.prefixar_sem_seguinte(Q.Concluida{r, s, False{}}, [Q.Entregue{bs}], {==},
              Fechos.prefixar_sem_seguinte(Q.Entregue{bs}, Nil{}, {==}, Fechos.vazio_sem_seguinte())), consulta)
        case True{}: sucessao_local_presente(s, r, bs, t, a, b, consulta)

def sucessao_depois_da_conclusao(+s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool,
  entrega: R.Entrega, +t: Nat, +a: D.Estado, +b: D.Estado,
  consulta: {Q.consultar(Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}, t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}) ->
  OrigemSeguinte(Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}, t, a, b):
  match entrega:
    case R.PendenteEntrega{}:
      negar_seguinte([Q.Concluida{r, s, fecha}], t, a, b,
        Fechos.prefixar_sem_seguinte(Q.Concluida{r, s, fecha}, Nil{}, {==}, Fechos.vazio_sem_seguinte()), consulta)
    case R.Quebrada{+prefixo}:
      negar_seguinte([Q.Concluida{r, s, fecha}, Q.Interrompida{prefixo}, Q.Fechada{}], t, a, b,
        Fechos.prefixar_sem_seguinte(Q.Concluida{r, s, fecha}, [Q.Interrompida{prefixo}, Q.Fechada{}], {==},
          Fechos.prefixar_sem_seguinte(Q.Interrompida{prefixo}, [Q.Fechada{}], {==},
            Fechos.prefixar_sem_seguinte(Q.Fechada{}, Nil{}, {==}, Fechos.vazio_sem_seguinte()))), consulta)
    case R.Completa{proxima}: sucessao_completa(s, r, bs, fecha, proxima, t, a, b, consulta)

def parte_anterior_da_conclusao(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>) -> List<&2, Q.Quadro>:
  Q.concatenar(antes, Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)})

def separar_conclusao(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +entrega: R.Entrega) ->
  {Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)) ==
    Q.concatenar(parte_anterior_da_conclusao(antes, s, r, bs), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}) : List<&2, Q.Quadro>}:
  Equal.sym(List<&2, Q.Quadro>,
    Q.concatenar(parte_anterior_da_conclusao(antes, s, r, bs), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}),
    Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)),
    Q.concatenar_assoc(antes, Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)},
      Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}))

def sucessao_da_parte(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +entrega: R.Entrega,
  +t: Nat, +a: D.Estado, +b: D.Estado,
  encontrado: &i: Nat -> L.E<{t == Nat.add(Q.tamanho(parte_anterior_da_conclusao(antes, s, r, bs)), i) : Nat},
    {Q.consultar(Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}, i) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}>) ->
  OrigemSeguinte(Q.concatenar(parte_anterior_da_conclusao(antes, s, r, bs),
    Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}), t, a, b):
  match encontrado:
    case (+i, L.Ambos{indice, consulta}):
      levantar_origem_seguinte(parte_anterior_da_conclusao(antes, s, r, bs),
        Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}, t, i, a, b, indice,
        sucessao_depois_da_conclusao(s, r, bs, fecha, entrega, i, a, b, consulta))

law sucessao_no_fecho:
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecha: Bool
  for +entrega: R.Entrega
  for +t: Nat
  for +a: D.Estado
  for +b: D.Estado
  for sem: Fechos.SemSeguinte(antes)
  for consulta: {Q.consultar(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}
  OrigemSeguinte(Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), t, a, b)
def sucessao_no_fecho(antes, s, r, bs, fecha, entrega, t, a, b, sem, consulta):
  %Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)),
    Q.concatenar(parte_anterior_da_conclusao(antes, s, r, bs), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}),
    separar_conclusao(antes, s, r, bs, fecha, entrega)) : OrigemSeguinte(_, t, a, b)
  sucessao_da_parte(antes, s, r, bs, fecha, entrega, t, a, b,
    Cinco.retirar_prefixo_sem_quadro(parte_anterior_da_conclusao(antes, s, r, bs),
      Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}, t, Q.Seguinte{a, b},
      Fechos.concatenar_sem_seguinte(antes, Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)}, sem,
        Fechos.prefixar_sem_seguinte(Q.Preparada{r, bs}, R.render_publicacao(r, s), {==}, Fechos.publicacao_sem_seguinte(r, s)))(a, b),
      (%separar_conclusao(antes, s, r, bs, fecha, entrega) : {Q.consultar(_, t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>} consulta)))

def origem_seguinte_vira_regra6(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +xs: List<&2, Q.Quadro>, -t: Nat, +anterior: D.Estado, -seguinte: D.Estado,
  origem: OrigemSeguinte(xs, t, anterior, seguinte),
  registrar: @u: Nat -> @r: S.Resposta -> @fecha: Bool ->
    {Q.consultar(xs, u) == Some{Q.Concluida{r, anterior, fecha}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Concluiu{r, anterior, fecha})) ->
  K.Regra6(I.ProximaChamada{anterior, seguinte}, a, k, x, t):
  match origem:
    case L.Ambos{igual, (+r, +fecha, +u, L.Ambos{ordem, consulta})}:
      L.Ambos{igual, (r, fecha, u, L.Ambos{ordem, registrar(u, r, fecha, consulta)})}

def sucessao_conforme_fecho(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +inicial: D.Estado, +recepcao: X.Recepcao, +antes: List<&2, Q.Quadro>, +s: D.Estado,
  +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +entrega: R.Entrega, +t: Nat, +a: D.Estado, +b: D.Estado,
  canonico: {I.Atender{mundo, c, inicial, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  mesma: {Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)) ==
    Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)) : List<&2, Q.Quadro>},
  sem: Fechos.SemSeguinte(antes),
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.ProximaChamada{a, b}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao}, t):
  F.com_par(K.Regra6(I.ProximaChamada{a, b}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao}, t),
    {Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)) : List<&2, Q.Quadro>},
    {Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)) : List<&2, Q.Quadro>},
    Chamada.duplicar_igualdade(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)),
      Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), mesma),
    observada => introduzir =>
      origem_seguinte_vira_regra6(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao},
        Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), t, a, b,
        sucessao_no_fecho(antes, s, r, bs, fecha, entrega, t, a, b, sem,
          (%observada : {Q.consultar(_, t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>} consulta)),
        +u => +rp => +f => presente => Ligacao.introduzir_na_lista(fonte, c, mundo, inicial, recepcao,
          Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), u,
          Q.Concluida{rp, a, f}, I.Concluiu{rp, a, f}, canonico, introduzir, presente, {==}, Unit{})))

def consumir_fecho_seguinte(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +inicial: D.Estado, +recepcao: X.Recepcao, +xs: List<&2, Q.Quadro>, +caso: R.Caso,
  +t: Nat, +a: D.Estado, +b: D.Estado,
  canonico: {I.Atender{mundo, c, inicial, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  mesma: {Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)) == xs : List<&2, Q.Quadro>},
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>},
  resultado: &h: Fechos.Fecho -> L.E<Fechos.Forma(xs, caso, Some{h}), Fechos.AntesSemSeguinte(Some{h})>) ->
  K.Regra6(I.ProximaChamada{a, b}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, recepcao}, t):
  match resultado:
    case (Fechos.Fecho{antes, N.Conclusao{s, r, bs}, fecha, entrega, origem},
      L.Ambos{L.Ambos{mesmo_caso, L.Ambos{traco, L.Ambos{pub, concl}}}, sem}):
      sucessao_conforme_fecho(fonte, c, mundo, inicial, recepcao, antes, s, r, bs, fecha, entrega, t, a, b, canonico,
        Equal.trans(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, recepcao, Fonte.chamada(fonte, mundo)), xs,
          Q.concatenar(antes, R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)), mesma, traco), sem, consulta)

def sucessao_por_guardas(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, +t: Nat, +a: D.Estado, +b: D.Estado,
  entrada: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
      Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, I.ProximaChamada{a, b})>>) ->
  K.Regra6(I.ProximaChamada{a, b}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match entrada:
    case L.Ambos{nome, L.Ambos{canonico, observado}}:
      F.com_par(K.Regra6(I.ProximaChamada{a, b}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        {Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>},
        {Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>},
        Chamada.duplicar_igualdade(Maybe<&2, Q.Quadro>, Q.consultar(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t), Some{Q.Seguinte{a, b}},
          Ligacao.quadro_da_observacao(fonte, c, s, recepcao, Fonte.chamada(fonte, mundo), t, I.ProximaChamada{a, b}, Unit{}, observado)),
        busca => consulta => consumir_fecho_seguinte(fonte, c, mundo, s, recepcao,
          R.render(Ligacao.micro_dos_dados(Fonte.chamada(fonte, mundo)), s, Ligacao.caso_dos_dados(c, recepcao, Fonte.chamada(fonte, mundo))),
          Ligacao.caso_dos_dados(c, recepcao, Fonte.chamada(fonte, mundo)), t, a, b, canonico,
          Ligacao.quadros_seguem_o_caso(c, s, recepcao, Fonte.chamada(fonte, mundo)), consulta,
          Fechos.inverter_seguinte(Ligacao.micro_dos_dados(Fonte.chamada(fonte, mundo)), s,
            Ligacao.caso_dos_dados(c, recepcao, Fonte.chamada(fonte, mundo)), t, a, b,
            (%Ligacao.quadros_seguem_o_caso(c, s, recepcao, Fonte.chamada(fonte, mundo)) :
              {Q.consultar(_, t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>} busca))))

law sucessao_da_fonte_obedece_regra6:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +recepcao: X.Recepcao
  for +t: Nat
  for +a: D.Estado
  for +b: D.Estado
  for observado: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.ProximaChamada{a, b})
  K.Regra6(I.ProximaChamada{a, b}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t)
def sucessao_da_fonte_obedece_regra6(fonte, c, mundo, s, recepcao, t, a, b, observado):
  sucessao_por_guardas(fonte, c, mundo, s, recepcao, t, a, b,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.ProximaChamada{a, b}, observado))


def inicial_nao_conclui_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +dados: Fonte.InicialData, +t: Nat, +r: S.Resposta, +w: D.Estado, +fecha: Bool,
  obs: Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados), t, I.Concluiu{r, w, fecha})) -> Empty:
  match dados:
    case Fonte.InicialData{cf, sf, pf, +j, +resultado, +micro}:
      Fases.ausente_exclui_consulta(Fases.Conclusao{}, R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro),
        t, Q.Concluida{r, w, fecha},
        L.e_esquerda({Fases.ausente(Fases.Conclusao{}, R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)) == True{} : Bool},
          Fechos.SemSeguinte(R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)),
          Fechos.exclusoes_do_inicio(micro, s, j, resultado, Config.valida(c, Fonte.identidade(fonte)))), {==},
        Q.observacao_quadro(c, Fonte.sem_programa(), R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro), t, I.Concluiu{r, w, fecha}, obs))

def inicial_nao_sucede_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +dados: Fonte.InicialData, +t: Nat, +a: D.Estado, +b: D.Estado,
  obs: Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados), t, I.ProximaChamada{a, b})) -> Empty:
  match dados:
    case Fonte.InicialData{cf, sf, pf, +j, +resultado, +micro}:
      L.e_direita({Fases.ausente(Fases.Conclusao{}, R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)) == True{} : Bool},
        Fechos.SemSeguinte(R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)),
        Fechos.exclusoes_do_inicio(micro, s, j, resultado, Config.valida(c, Fonte.identidade(fonte))))(a, b, t,
          Q.observacao_quadro(c, Fonte.sem_programa(), R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro), t, I.ProximaChamada{a, b}, obs))

def conclusao_inicial_e_impossivel(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +t: Nat, +r: S.Resposta, +w: D.Estado, +fecha: Bool,
  obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.Concluiu{r, w, fecha})) -> Empty:
  inicial_nao_conclui_dados(fonte, c, s, Fonte.inicial(fonte, mundo), t, r, w, fecha,
    Ref.retirar_guardas({Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
      {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
      Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, I.Concluiu{r, w, fecha}),
      Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.Concluiu{r, w, fecha}, obs)))

def sucessao_inicial_e_impossivel(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +t: Nat, +a: D.Estado, +b: D.Estado,
  obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.ProximaChamada{a, b})) -> Empty:
  inicial_nao_sucede_dados(fonte, c, s, Fonte.inicial(fonte, mundo), t, a, b,
    Ref.retirar_guardas({Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
      {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
      Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, I.ProximaChamada{a, b}),
      Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.ProximaChamada{a, b}, obs)))

def regra6_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, +mundo: Nat, +t: Nat, f: I.Fato,
  origem: PublicacaoServico.OrigemDoMomento(fonte, c, seed, historico, mundo, Cenarios.Inicializacao{}),
  obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, seed(Unit{}), pi}, t, f)) ->
  K.Regra6(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, seed(Unit{}), pi}, t):
  match f:
    case I.Publicou{w}: PublicacaoServico.publicacao_por_momento(fonte, c, seed, historico, pi, mundo, Cenarios.Inicializacao{}, t, w, origem, obs)
    case I.EstadoVisivel{w}: Vis.visibilidade_inicial_fonte_obedece_regra6(fonte, c, mundo, seed(Unit{}), pi, t, w, obs)
    case I.Concluiu{r, w, fecha}:
      L.ex_falso(K.Regra6(I.Concluiu{r, w, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, seed(Unit{}), pi}, t),
        conclusao_inicial_e_impossivel(fonte, c, mundo, seed(Unit{}), pi, t, r, w, fecha, obs))
    case I.ProximaChamada{a, b}:
      L.ex_falso(K.Regra6(I.ProximaChamada{a, b}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, seed(Unit{}), pi}, t),
        sucessao_inicial_e_impossivel(fonte, c, mundo, seed(Unit{}), pi, t, a, b, obs))
    case I.ConfiguracaoEmUso{a0}: Unit{}
    case I.InspecaoNaoModelada{a0}: Unit{}
    case I.EfeitoNaoModelado{a0}: Unit{}
    case I.InstanciaIniciou{a0}: Unit{}
    case I.InicializacaoRecusada{a0}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{a0, a1}: Unit{}
    case I.Decodificou{a0, a1}: Unit{}
    case I.Guardou{a0, a1, a2}: Unit{}
    case I.Operou{a0, a1, a2, a3}: Unit{}
    case I.ConferiuComprimento{a0, a1}: Unit{}
    case I.AlocouCampo{a0, a1}: Unit{}
    case I.LeuCorpo{a0, a1, a2}: Unit{}
    case I.RecebeuRequisicao{a0}: Unit{}
    case I.Autenticou{a0, a1}: Unit{}
    case I.CertificadoAceito{a0, a1, a2}: Unit{}
    case I.CertificadoRejeitado{a0, a1}: Unit{}
    case I.ProgramaComecou{a0, a1, a2}: Unit{}
    case I.Avaliou{a0, a1, a2, a3}: Unit{}
    case I.Preparou{a0, a1}: Unit{}
    case I.FalhouAmbiente{a0, a1, a2}: Unit{}
    case I.EntregouTudo{a0}: Unit{}
    case I.EntregaInterrompida{a0}: Unit{}
    case I.EncerrouCanal{}: Unit{}

def regra6_atendimento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, +mundo: Nat, +recepcao: X.Recepcao, +t: Nat, f: I.Fato,
  origem: PublicacaoServico.OrigemDoMomento(fonte, c, seed, historico, mundo, Cenarios.Atendimento{recepcao}),
  obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte),
    I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), recepcao}, t, f)) ->
  K.Regra6(f, Fonte.ambiente(fonte), Fonte.artefato(fonte),
    I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), recepcao}, t):
  match f:
    case I.Publicou{w}: PublicacaoServico.publicacao_por_momento(fonte, c, seed, historico, pi, mundo, Cenarios.Atendimento{recepcao}, t, w, origem, obs)
    case I.EstadoVisivel{w}: Vis.visibilidade_atendimento_fonte_obedece_regra6(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), recepcao, t, w, obs)
    case I.Concluiu{r, w, fecha}: conclusao_da_fonte_obedece_regra6(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), recepcao, t, r, w, fecha, obs)
    case I.ProximaChamada{a, b}: sucessao_da_fonte_obedece_regra6(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), recepcao, t, a, b, obs)
    case I.ConfiguracaoEmUso{a0}: Unit{}
    case I.InspecaoNaoModelada{a0}: Unit{}
    case I.EfeitoNaoModelado{a0}: Unit{}
    case I.InstanciaIniciou{a0}: Unit{}
    case I.InicializacaoRecusada{a0}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{a0, a1}: Unit{}
    case I.Decodificou{a0, a1}: Unit{}
    case I.Guardou{a0, a1, a2}: Unit{}
    case I.Operou{a0, a1, a2, a3}: Unit{}
    case I.ConferiuComprimento{a0, a1}: Unit{}
    case I.AlocouCampo{a0, a1}: Unit{}
    case I.LeuCorpo{a0, a1, a2}: Unit{}
    case I.RecebeuRequisicao{a0}: Unit{}
    case I.Autenticou{a0, a1}: Unit{}
    case I.CertificadoAceito{a0, a1, a2}: Unit{}
    case I.CertificadoRejeitado{a0, a1}: Unit{}
    case I.ProgramaComecou{a0, a1, a2}: Unit{}
    case I.Avaliou{a0, a1, a2, a3}: Unit{}
    case I.Preparou{a0, a1}: Unit{}
    case I.FalhouAmbiente{a0, a1, a2}: Unit{}
    case I.EntregouTudo{a0}: Unit{}
    case I.EntregaInterrompida{a0}: Unit{}
    case I.EncerrouCanal{}: Unit{}

def regra6_no_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, +mundo: Nat, +momento: Cenarios.Momento,
  +t: Nat, f: I.Fato, origem: PublicacaoServico.OrigemDoMomento(fonte, c, seed, historico, mundo, momento),
  obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t, f)) ->
  K.Regra6(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t):
  match momento:
    case Cenarios.Inicializacao{}: regra6_inicial(fonte, c, seed, historico, pi, mundo, t, f, origem, obs)
    case Cenarios.Atendimento{r}: regra6_atendimento(fonte, c, seed, historico, pi, mundo, r, t, f, origem, obs)

def fato_no_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, +mundo: Nat, +momento: Cenarios.Momento,
  -t: Nat, -f: I.Fato,
  canonico: {Fonte.cenario(fonte, mundo) == Cenarios.de_momento(c, seed, historico, pi, momento, mundo) : I.Cenario},
  observado: Fonte.da_rota(fonte, Fonte.cenario(fonte, mundo), t, f)) ->
  I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t, f):
  match momento:
    case Cenarios.Inicializacao{}:
      Fonte.introduzir_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, seed(Unit{}), pi}, t, f,
        L.Ambos{{==}, Fonte.origem_literal(fonte, I.Inicializar{mundo, c, seed(Unit{}), pi}, Fonte.cenario(fonte, mundo), t, f,
          Equal.sym(I.Cenario, Fonte.cenario(fonte, mundo), I.Inicializar{mundo, c, seed(Unit{}), pi}, canonico), observado)})
    case Cenarios.Atendimento{+r}:
      Fonte.introduzir_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), r}, t, f,
        L.Ambos{{==}, Fonte.origem_literal(fonte, I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), r}, Fonte.cenario(fonte, mundo), t, f,
          Equal.sym(I.Cenario, Fonte.cenario(fonte, mundo), I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), r}, canonico), observado)})

def regra6_da_origem(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  -x: I.Cenario, +mundo: Nat, +t: Nat, f: I.Fato,
  origem: PublicacaoServico.OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, mundo, momento(mundo)),
  observado: L.E<{Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)) == Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)) : String},
    L.E<{x == Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo) : I.Cenario},
      Fonte.da_rota(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo), t, f)>>) ->
  K.Regra6(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t):
  match observado:
    case L.Ambos{nome, L.Ambos{igual, raw}}:
      %Equal.sym(I.Cenario, x, Cenarios.canonico(c, seed, historico, momento, pi, mundo),
        Equal.trans(I.Cenario, x, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo),
          Cenarios.canonico(c, seed, historico, momento, pi, mundo), igual, Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo))) :
        K.Regra6(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), _, t)
      regra6_no_momento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, pi, mundo, momento(mundo), t, f, origem,
        fato_no_momento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, pi, mundo, momento(mundo), t, f,
          Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo), raw))

def lei6_do_cenario(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @m: Nat -> PublicacaoServico.OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m)),
  x: I.Cenario, +t: Nat, f: I.Fato,
  observado: I.Acontece(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t, f)) ->
  K.Regra6(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t):
  match x:
    case I.Inicializar{+m, original, +s, +prova}:
      regra6_da_origem(base, c, seed, historico, momento, pi, I.Inicializar{m, original, s, prova}, m, t, f, origens(m),
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Inicializar{m, original, s, prova}, t, f, observado))
    case I.Atender{+m, original, +s, +recepcao}:
      regra6_da_origem(base, c, seed, historico, momento, pi, I.Atender{m, original, s, recepcao}, m, t, f, origens(m),
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Atender{m, original, s, recepcao}, t, f, observado))

def lei6_do_modelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @m: Nat -> PublicacaoServico.OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m))) ->
  K.Lei6(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi))):
  x => +t => f => observado => lei6_do_cenario(base, c, seed, historico, momento, pi, origens, x, t, f, observado)
