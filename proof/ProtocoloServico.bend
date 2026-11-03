# API de pesquisa: consultas a UMA rota fixa; nao demonstra validade da rota.
import Base
import ../contrato/Protocolo.bend as P
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Interface.bend as I
import ../contrato/Recursos.bend as X
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F

# Programas e configuracao nao sao copiados nos quadros.
type Quadro is Data:
  Configurada{}
  InicialAceita{}
  Iniciada{estado: D.Estado}
  InicialRecusada{status: S.Status}
  Codificada{valor: D.Valor, bytes: Maybe<&2, List<&2, U32>>}
  Decodificada{bytes: List<&2, U32>, valor: Maybe<&2, D.Valor>}
  Guardada{estado: D.Estado, bytes: List<&2, U32>, abstracao: D.Estado}
  Conferida{posicao: Nat, quantidade: Nat}
  Construida{posicao: Nat, quantidade: Nat}
  Lida{antes: Nat, quantidade: Nat, declarado: Nat}
  Recebida{requisicao: P.Requisicao}
  Autenticada{requisicao: P.Requisicao, contexto: Maybe<&2, D.Contexto>}
  Aceita{requisicao: P.Requisicao, contexto: D.Contexto}
  Rejeitada{requisicao: P.Requisicao, contexto: D.Contexto}
  Comecada{requisicao: P.Requisicao, contexto: D.Contexto}
  Avaliada{requisicao: P.Requisicao, contexto: D.Contexto, percurso: S.Percurso}
  Operada{esquema: D.Esquema, estado: D.Estado, operacao: D.Operacao, resultado: D.ResultadoOp}
  Preparada{resposta: S.Resposta, bytes: List<&2, U32>}
  Publicada{estado: D.Estado}
  Visivel{estado: D.Estado}
  Falhou{etapa: X.Etapa, identificador: String, fatal: Bool}
  Concluida{resposta: S.Resposta, estado: D.Estado, fecha: Bool}
  Entregue{bytes: List<&2, U32>}
  Interrompida{prefixo: List<&2, U32>}
  Fechada{}
  Seguinte{anterior: D.Estado, inicial: D.Estado}
  Inspecao{descricao: String}
  Efeito{descricao: String}

# Fato canonico do quadro, com os indices publicos da configuracao e programa.
def fato_do_quadro(c: S.Configuracao, p: S.Programa, q: Quadro) -> I.Fato:
  match q:
    case Configurada{}: I.ConfiguracaoEmUso{c}
    case InicialAceita{}: I.ProvaInicialAceita{}
    case Iniciada{s}: I.InstanciaIniciou{s}
    case InicialRecusada{s}: I.InicializacaoRecusada{s}
    case Codificada{v, bs}: I.Codificou{v, bs}
    case Decodificada{bs, v}: I.Decodificou{bs, v}
    case Guardada{s, bs, abstr}: I.Guardou{s, bs, abstr}
    case Conferida{pos, n}: I.ConferiuComprimento{pos, n}
    case Construida{pos, n}: I.AlocouCampo{pos, n}
    case Lida{antes, n, declarado}: I.LeuCorpo{antes, n, declarado}
    case Recebida{r}: I.RecebeuRequisicao{r}
    case Autenticada{r, ctx}: I.Autenticou{r, ctx}
    case Aceita{r, ctx}: I.CertificadoAceito{r, ctx, p}
    case Rejeitada{r, ctx}: I.CertificadoRejeitado{r, ctx}
    case Comecada{r, ctx}: I.ProgramaComecou{r, ctx, p}
    case Avaliada{r, ctx, percurso}: I.Avaliou{r, ctx, p, percurso}
    case Operada{e, s, o, r}: I.Operou{e, s, o, r}
    case Preparada{r, bs}: I.Preparou{r, bs}
    case Publicada{s}: I.Publicou{s}
    case Visivel{s}: I.EstadoVisivel{s}
    case Falhou{etapa, id, fatal}: I.FalhouAmbiente{etapa, id, fatal}
    case Concluida{r, s, fecha}: I.Concluiu{r, s, fecha}
    case Entregue{bs}: I.EntregouTudo{bs}
    case Interrompida{bs}: I.EntregaInterrompida{bs}
    case Fechada{}: I.EncerrouCanal{}
    case Seguinte{antes, apos}: I.ProximaChamada{antes, apos}
    case Inspecao{descricao}: I.InspecaoNaoModelada{descricao}
    case Efeito{descricao}: I.EfeitoNaoModelado{descricao}

def rel_fato(-c: S.Configuracao, -p: S.Programa, q: Quadro, -f: I.Fato) -> Type:
  {f == fato_do_quadro(c, p, q) : I.Fato}

def consultar(xs: List<&2, Quadro>, n: Nat) -> Maybe<&2, Quadro>:
  match xs n:
    case Nil{} _: None{}
    case Con{h, t} 0n: Some{h}
    case Con{h, t} 1n+k: consultar(t, k)

def selecionado(-c: S.Configuracao, -p: S.Programa, q: Maybe<&2, Quadro>, -f: I.Fato) -> Type:
  match q:
    case None{}: Empty
    case Some{frame}: rel_fato(c, p, frame, f)

def observa(-c: S.Configuracao, -p: S.Programa, xs: List<&2, Quadro>, t: Nat, -f: I.Fato) -> Type:
  selecionado(c, p, consultar(xs, t), f)

law cabeca:
  for -h: Quadro
  for -t: List<&2, Quadro>
  {consultar(Con{h, t}, 0n) == Some{h} : Maybe<&2, Quadro>}
def cabeca(h, t):
  {==}

law cauda:
  for -h: Quadro
  for -t: List<&2, Quadro>
  for -n: Nat
  {consultar(Con{h, t}, 1n+n) == consultar(t, n) : Maybe<&2, Quadro>}
def cauda(h, t, n):
  {==}

law consulta_unica:
  for -xs: List<&2, Quadro>
  for -t: Nat
  for +a: Quadro
  for -b: Quadro
  for ha: {consultar(xs, t) == Some{a} : Maybe<&2, Quadro>}
  for hb: {consultar(xs, t) == Some{b} : Maybe<&2, Quadro>}
  {a == b : Quadro}
def consulta_unica(xs, t, a, b, ha, hb):
  F.algum_injetivo(Quadro, a, b,
    Equal.trans(Maybe<&2, Quadro>, Some{a}, consultar(xs, t), Some{b},
      Equal.sym(Maybe<&2, Quadro>, consultar(xs, t), Some{a}, ha), hb))

# Concatena subtracos; os indices deslocam pelo numero real de quadros.
def concatenar(xs: List<&2, Quadro>, ys: List<&2, Quadro>) -> List<&2, Quadro>:
  match xs:
    case Nil{}: ys
    case Con{h, t}: Con{h, concatenar(t, ys)}

def tamanho(xs: List<&2, Quadro>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{h, t}: 1n+tamanho(t)

law consultar_apos_prefixo:
  for xs: List<&2, Quadro>
  for -ys: List<&2, Quadro>
  for -n: Nat
  {consultar(concatenar(xs, ys), Nat.add(tamanho(xs), n)) == consultar(ys, n) : Maybe<&2, Quadro>}
def consultar_apos_prefixo(xs, ys, n):
  match xs:
    case Nil{}: {==}
    case Con{h, t}: consultar_apos_prefixo(t, ys, n)

law consultar_dentro_prefixo:
  for xs: List<&2, Quadro>
  for -ys: List<&2, Quadro>
  for n: Nat
  for dentro: {Nat.is_lt(n, tamanho(xs)) == True{} : Bool}
  {consultar(concatenar(xs, ys), n) == consultar(xs, n) : Maybe<&2, Quadro>}
def consultar_dentro_prefixo(xs, ys, n, dentro):
  match xs n:
    case Nil{} 0n:
      F.absurdo_booleano({consultar(concatenar(Nil{}, ys), 0n) == consultar(Nil{}, 0n) : Maybe<&2, Quadro>}, dentro)
    case Nil{} 1n+k:
      F.absurdo_booleano({consultar(concatenar(Nil{}, ys), 1n+k) == consultar(Nil{}, 1n+k) : Maybe<&2, Quadro>}, dentro)
    case Con{h, t} 0n: {==}
    case Con{h, t} 1n+k: consultar_dentro_prefixo(t, ys, k, dentro)

# Uma consulta presente continua igual ao acrescentar quadros ao fim.
# A inducao evita calcular um limite e duplicar a igualdade da consulta.
law consulta_prefixo:
  for +xs: List<&2, Quadro>
  for -ys: List<&2, Quadro>
  for +t: Nat
  for -q: Quadro
  for presente: {consultar(xs, t) == Some{q} : Maybe<&2, Quadro>}
  {consultar(concatenar(xs, ys), t) == Some{q} : Maybe<&2, Quadro>}
def consulta_prefixo(xs, ys, t, q, presente):
  match xs t:
    case Nil{} _:
      L.ex_falso({consultar(concatenar(Nil{}, ys), t) == Some{q} : Maybe<&2, Quadro>},
        F.nenhum_nao_algum(Quadro, q, presente))
    case Con{h, cauda} 0n: presente
    case Con{h, cauda} 1n+n: consulta_prefixo(cauda, ys, n, q, presente)

law posicao_presente_dentro:
  for xs: List<&2, Quadro>
  for n: Nat
  for -q: Quadro
  for presente: {consultar(xs, n) == Some{q} : Maybe<&2, Quadro>}
  {Nat.is_lt(n, tamanho(xs)) == True{} : Bool}
def posicao_presente_dentro(xs, n, q, presente):
  match xs n:
    case Nil{} _:
      L.ex_falso({Nat.is_lt(n, tamanho(Nil{})) == True{} : Bool}, F.nenhum_nao_algum(Quadro, q, presente))
    case Con{h, t} 0n: {==}
    case Con{h, t} 1n+k: posicao_presente_dentro(t, k, q, presente)

law consulta_estabelece_observacao:
  for -c: S.Configuracao
  for -p: S.Programa
  for -xs: List<&2, Quadro>
  for -t: Nat
  for -q: Quadro
  for -f: I.Fato
  for consulta: {consultar(xs, t) == Some{q} : Maybe<&2, Quadro>}
  for fato: rel_fato(c, p, q, f)
  observa(c, p, xs, t, f)
def consulta_estabelece_observacao(c, p, xs, t, q, f, consulta, fato):
  %Equal.sym(Maybe<&2, Quadro>, consultar(xs, t), Some{q}, consulta) : selecionado(c, p, _, f)
  fato

# Subtraco do nucleo: nao consegue introduzir publicacao/conclusao.
type QuadroExec is Data:
  Avaliacao{percurso: S.Percurso}
  Operacao{esquema: D.Esquema, estado: D.Estado, operacao: D.Operacao, resultado: D.ResultadoOp}

def expandir_exec(+r: P.Requisicao, +ctx: D.Contexto, xs: List<&2, QuadroExec>) -> List<&2, Quadro>:
  match xs:
    case Nil{}: Nil{}
    case Con{Avaliacao{percurso}, t}: Con{Avaliada{r, ctx, percurso}, expandir_exec(r, ctx, t)}
    case Con{Operacao{e, s, o, resultado}, t}: Con{Operada{e, s, o, resultado}, expandir_exec(r, ctx, t)}

# Estado persistente antes do tick; nao um relato escolhido pelo candidato.
def atualizar_estado(q: Quadro, anterior: Maybe<&2, D.Estado>) -> Maybe<&2, D.Estado>:
  match q:
    case Iniciada{s}: Some{s}
    case Publicada{s}: Some{s}
    case _: anterior

def estado_em(xs: List<&2, Quadro>, t: Nat, anterior: Maybe<&2, D.Estado>) -> Maybe<&2, D.Estado>:
  match xs t:
    case Nil{} _: anterior
    case Con{h, tail} 0n: anterior
    case Con{h, tail} 1n+k: estado_em(tail, k, atualizar_estado(h, anterior))

def estado_inicial(x: I.Cenario) -> Maybe<&2, D.Estado>:
  match x:
    case I.Inicializar{mundo, c, s, pi}: None{}
    case I.Atender{mundo, c, s, entrada}: Some{s}

def visivel(q: Maybe<&2, D.Estado>, -s: D.Estado) -> Type:
  match q:
    case None{}: Empty
    case Some{atual}: {s == atual : D.Estado}

# O indice e uma posicao do protocolo, nunca um relogio ou orcamento.
# Uma falha fatal encerra a disponibilidade da instancia, sem desfazer stores.
def falha_fatal(q: Quadro) -> Bool:
  match q:
    case Falhou{etapa, id, fatal}: fatal
    case _: False{}

def instancia_ativa(xs: List<&2, Quadro>, t: Nat) -> Bool:
  match xs t:
    case Nil{} _: True{}
    case Con{h, r} 0n: True{}
    case Con{h, r} 1n+k: Bool.not(falha_fatal(h)) && instancia_ativa(r, k)

def posicao_observavel(+xs: List<&2, Quadro>, +t: Nat) -> Bool:
  Nat.is_le(t, tamanho(xs)) && instancia_ativa(xs, t)

def observa_servico(-c: S.Configuracao, -p: S.Programa, inicial: Maybe<&2, D.Estado>,
  xs: List<&2, Quadro>, t: Nat, f: I.Fato) -> Type:
  match f:
    case I.ConfiguracaoEmUso{original}: L.E<{posicao_observavel(xs, t) == True{} : Bool}, {original == c : S.Configuracao}>
    case I.EstadoVisivel{s}: L.E<{posicao_observavel(xs, t) == True{} : Bool}, visivel(estado_em(xs, t, inicial), s)>
    case _: observa(c, p, xs, t, f)

law estado_antes_do_primeiro_passo:
  for xs: List<&2, Quadro>
  for -s: Maybe<&2, D.Estado>
  {estado_em(xs, 0n, s) == s : Maybe<&2, D.Estado>}
def estado_antes_do_primeiro_passo(xs, s):
  match xs:
    case Nil{}: {==}
    case Con{h, t}: {==}

law publicar_muda_so_o_estado_seguinte:
  for -xs: List<&2, Quadro>
  for -s: Maybe<&2, D.Estado>
  for -w: D.Estado
  for -t: Nat
  {estado_em(Con{Publicada{w}, xs}, 1n+t, s) == estado_em(xs, t, Some{w}) : Maybe<&2, D.Estado>}
def publicar_muda_so_o_estado_seguinte(xs, s, w, t):
  {==}


# Unicidade do evento selecionado, sem exigir que o fato seja Data.
def rel_fato_unico(-c: S.Configuracao, -p: S.Programa, q: Quadro,
  -f: I.Fato, -g: I.Fato, hf: rel_fato(c, p, q, f), hg: rel_fato(c, p, q, g)) ->
  {f == g : I.Fato}:
  Equal.trans(I.Fato, f, fato_do_quadro(c, p, q), g, hf,
    Equal.sym(I.Fato, g, fato_do_quadro(c, p, q), hg))

def selecionado_unico(-c: S.Configuracao, -p: S.Programa, q: Maybe<&2, Quadro>,
  -f: I.Fato, -g: I.Fato, hf: selecionado(c, p, q, f), hg: selecionado(c, p, q, g)) ->
  {f == g : I.Fato}:
  match q:
    case None{}: L.ex_falso({f == g : I.Fato}, hf)
    case Some{frame}: rel_fato_unico(c, p, frame, f, g, hf, hg)

law observacao_unica:
  for -c: S.Configuracao
  for -p: S.Programa
  for xs: List<&2, Quadro>
  for t: Nat
  for -f: I.Fato
  for -g: I.Fato
  for hf: observa(c, p, xs, t, f)
  for hg: observa(c, p, xs, t, g)
  {f == g : I.Fato}
def observacao_unica(c, p, xs, t, f, g, hf, hg):
  selecionado_unico(c, p, consultar(xs, t), f, g, hf, hg)


# Projecao esquece apenas os indices Type (configuracao/programa).
def quadro_do_fato(f: I.Fato) -> Quadro:
  match f:
    case I.ConfiguracaoEmUso{c}: Configurada{}
    case I.ProvaInicialAceita{}: InicialAceita{}
    case I.InstanciaIniciou{s}: Iniciada{s}
    case I.InicializacaoRecusada{s}: InicialRecusada{s}
    case I.Codificou{v, bs}: Codificada{v, bs}
    case I.Decodificou{bs, v}: Decodificada{bs, v}
    case I.Guardou{s, bs, abstr}: Guardada{s, bs, abstr}
    case I.ConferiuComprimento{pos, n}: Conferida{pos, n}
    case I.AlocouCampo{pos, n}: Construida{pos, n}
    case I.LeuCorpo{antes, n, declarado}: Lida{antes, n, declarado}
    case I.RecebeuRequisicao{r}: Recebida{r}
    case I.Autenticou{r, ctx}: Autenticada{r, ctx}
    case I.CertificadoAceito{r, ctx, p}: Aceita{r, ctx}
    case I.CertificadoRejeitado{r, ctx}: Rejeitada{r, ctx}
    case I.ProgramaComecou{r, ctx, p}: Comecada{r, ctx}
    case I.Avaliou{r, ctx, p, percurso}: Avaliada{r, ctx, percurso}
    case I.Operou{e, s, o, r}: Operada{e, s, o, r}
    case I.Preparou{r, bs}: Preparada{r, bs}
    case I.Publicou{s}: Publicada{s}
    case I.EstadoVisivel{s}: Visivel{s}
    case I.FalhouAmbiente{etapa, id, fatal}: Falhou{etapa, id, fatal}
    case I.Concluiu{r, s, fecha}: Concluida{r, s, fecha}
    case I.EntregouTudo{bs}: Entregue{bs}
    case I.EntregaInterrompida{bs}: Interrompida{bs}
    case I.EncerrouCanal{}: Fechada{}
    case I.ProximaChamada{antes, apos}: Seguinte{antes, apos}
    case I.InspecaoNaoModelada{descricao}: Inspecao{descricao}
    case I.EfeitoNaoModelado{descricao}: Efeito{descricao}

# A projecao esquece os indices e recupera exatamente o quadro original.
def fato_reconstroi_quadro(-c: S.Configuracao, -p: S.Programa, q: Quadro) ->
  {quadro_do_fato(fato_do_quadro(c, p, q)) == q : Quadro}:
  match q:
    case Configurada{}: {==}
    case InicialAceita{}: {==}
    case Iniciada{s}: {==}
    case InicialRecusada{s}: {==}
    case Codificada{v, bs}: {==}
    case Decodificada{bs, v}: {==}
    case Guardada{s, bs, abstr}: {==}
    case Conferida{pos, n}: {==}
    case Construida{pos, n}: {==}
    case Lida{antes, n, declarado}: {==}
    case Recebida{r}: {==}
    case Autenticada{r, ctx}: {==}
    case Aceita{r, ctx}: {==}
    case Rejeitada{r, ctx}: {==}
    case Comecada{r, ctx}: {==}
    case Avaliada{r, ctx, percurso}: {==}
    case Operada{e, s, o, r}: {==}
    case Preparada{r, bs}: {==}
    case Publicada{s}: {==}
    case Visivel{s}: {==}
    case Falhou{etapa, id, fatal}: {==}
    case Concluida{r, s, fecha}: {==}
    case Entregue{bs}: {==}
    case Interrompida{bs}: {==}
    case Fechada{}: {==}
    case Seguinte{antes, apos}: {==}
    case Inspecao{descricao}: {==}
    case Efeito{descricao}: {==}

def relacao_quadro(-c: S.Configuracao, -p: S.Programa, q: Quadro,
  -f: I.Fato, hf: rel_fato(c, p, q, f)) -> {quadro_do_fato(f) == q : Quadro}:
  %Equal.sym(I.Fato, f, fato_do_quadro(c, p, q), hf) : {quadro_do_fato(_) == q : Quadro}
  fato_reconstroi_quadro(c, p, q)

def selecionado_quadro(-c: S.Configuracao, -p: S.Programa, q: Maybe<&2, Quadro>,
  -f: I.Fato, hf: selecionado(c, p, q, f)) -> {q == Some{quadro_do_fato(f)} : Maybe<&2, Quadro>}:
  match q:
    case None{}: L.ex_falso({None{} == Some{quadro_do_fato(f)} : Maybe<&2, Quadro>}, hf)
    case Some{+frame}:
      Equal.cong(Quadro, Maybe<&2, Quadro>, q => Some{q}, frame, quadro_do_fato(f),
        Equal.sym(Quadro, quadro_do_fato(f), frame, relacao_quadro(c, p, frame, f, hf)))

law observacao_quadro:
  for -c: S.Configuracao
  for -p: S.Programa
  for xs: List<&2, Quadro>
  for t: Nat
  for -f: I.Fato
  for hf: observa(c, p, xs, t, f)
  {consultar(xs, t) == Some{quadro_do_fato(f)} : Maybe<&2, Quadro>}
def observacao_quadro(c, p, xs, t, f, hf):
  selecionado_quadro(c, p, consultar(xs, t), f, hf)

# Decomposicao generica de consulta em duas fases concatenadas.
def Parte(-xs: List<&2, Quadro>, -ys: List<&2, Quadro>, -t: Nat, -q: Quadro) -> Type:
  L.Ou<&i: Nat -> L.E<{t == i : Nat}, {consultar(xs, i) == Some{q} : Maybe<&2, Quadro>}>,
    &i: Nat -> L.E<{t == Nat.add(tamanho(xs), i) : Nat}, {consultar(ys, i) == Some{q} : Maybe<&2, Quadro>}>>

def levantar_parte(-h: Quadro, -xs: List<&2, Quadro>, -ys: List<&2, Quadro>,
  -t: Nat, -q: Quadro, parte: Parte(xs, ys, t, q)) -> Parte(Con{h, xs}, ys, Succ{t}, q):
  match parte:
    case L.Esquerda{(i, L.Ambos{pos, consulta})}:
      L.Esquerda{(Succ{i}, L.Ambos{Equal.cong(Nat, Nat, x => Succ{x}, t, i, pos), consulta})}
    case L.Direita{(i, L.Ambos{pos, consulta})}:
      L.Direita{(i, L.Ambos{Equal.cong(Nat, Nat, x => Succ{x}, t, Nat.add(tamanho(xs), i), pos), consulta})}

law dividir_consulta:
  for +xs: List<&2, Quadro>
  for -ys: List<&2, Quadro>
  for t: Nat
  for -q: Quadro
  for consulta: {consultar(concatenar(xs, ys), t) == Some{q} : Maybe<&2, Quadro>}
  Parte(xs, ys, t, q)
def dividir_consulta(xs, ys, t, q, consulta):
  match xs t:
    case Nil{} +u: L.Direita{(u, L.Ambos{{==}, consulta})}
    case Con{h, r} 0n: L.Esquerda{(0n, L.Ambos{{==}, consulta})}
    case Con{h, +r} 1n+u: levantar_parte(h, r, ys, u, q, dividir_consulta(r, ys, u, q, consulta))

law ordem_deslocada:
  for prefixo: Nat
  for -a: Nat
  for -b: Nat
  for menor: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(prefixo, a), Nat.add(prefixo, b)) == True{} : Bool}
def ordem_deslocada(prefixo, a, b, menor):
  match prefixo:
    case 0n: menor
    case 1n+p: ordem_deslocada(p, a, b, menor)


law concatenar_assoc:
  for xs: List<&2, Quadro>
  for -ys: List<&2, Quadro>
  for -zs: List<&2, Quadro>
  {concatenar(concatenar(xs, ys), zs) == concatenar(xs, concatenar(ys, zs)) : List<&2, Quadro>}
def concatenar_assoc(xs, ys, zs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, Quadro>, List<&2, Quadro>, r => Con{h, r},
        concatenar(concatenar(t, ys), zs), concatenar(t, concatenar(ys, zs)), concatenar_assoc(t, ys, zs))

# Cada relacao selecionada e uma igualdade de fatos. J permite reabrir esta
# igualdade duas vezes; nenhum Programa/Configuracao vivo e duplicado.
def igualdade_reabrivel(-A: Type, -x: A, -y: A, igual: {x == y : A}) ->
  L.E<{x == y : A}, {x == y : A}>:
  %igual : L.E<{x == _ : A}, {x == _ : A}>
  L.Ambos{{==}, {==}}

def duplicar_rel_fato(-c: S.Configuracao, -p: S.Programa, q: Quadro, -f: I.Fato,
  fato: rel_fato(c, p, q, f)) -> L.E<rel_fato(c, p, q, f), rel_fato(c, p, q, f)>:
  igualdade_reabrivel(I.Fato, f, fato_do_quadro(c, p, q), fato)

def duplicar_selecionado(-c: S.Configuracao, -p: S.Programa, q: Maybe<&2, Quadro>, -f: I.Fato,
  fato: selecionado(c, p, q, f)) -> L.E<selecionado(c, p, q, f), selecionado(c, p, q, f)>:
  match q:
    case None{}: L.ex_falso(L.E<Empty, Empty>, fato)
    case Some{q}: duplicar_rel_fato(c, p, q, f, fato)

law duplicar_observacao:
  for -c: S.Configuracao
  for -p: S.Programa
  for xs: List<&2, Quadro>
  for t: Nat
  for -f: I.Fato
  for fato: observa(c, p, xs, t, f)
  L.E<observa(c, p, xs, t, f), observa(c, p, xs, t, f)>
def duplicar_observacao(c, p, xs, t, f, fato):
  duplicar_selecionado(c, p, consultar(xs, t), f, fato)

# Dois marcos consecutivos depois de um prefixo, sem convencao de slots vazios.
law dois_quadros_apos_prefixo:
  for xs: List<&2, Quadro>
  for -ys: List<&2, Quadro>
  for -a: Quadro
  for -b: Quadro
  L.E<{consultar(concatenar(xs, Con{a, Con{b, ys}}), tamanho(xs)) == Some{a} : Maybe<&2, Quadro>},
    {consultar(concatenar(xs, Con{a, Con{b, ys}}), Succ{tamanho(xs)}) == Some{b} : Maybe<&2, Quadro>}>
def dois_quadros_apos_prefixo(xs, ys, a, b):
  match xs:
    case Nil{}: L.Ambos{{==}, {==}}
    case Con{h, t}: dois_quadros_apos_prefixo(t, ys, a, b)

# Aritmetica de ordem usada pelos prefixos e pela execucao.
law menor_transitivo:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}
def menor_transitivo(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _: F.absurdo_booleano({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 0n 1n+j 0n: F.absurdo_booleano({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 1n+j 1n+k: {==}
    case 1n+i 0n _: F.absurdo_booleano({Nat.is_lt(1n+i, c) == True{} : Bool}, ab)
    case 1n+i 1n+j 0n: F.absurdo_booleano({Nat.is_lt(1n+i, 0n) == True{} : Bool}, bc)
    case 1n+i 1n+j 1n+k: menor_transitivo(i, j, k, ab, bc)


# Prefixo dos fatos efetivamente observados quando uma chamada e interrompida.
# Nao e prazo, fuel ou limite de execucao.
def primeiros(n: Nat, xs: List<&2, Quadro>) -> List<&2, Quadro>:
  match n xs:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k Con{h, t}: Con{h, primeiros(k, t)}

law consulta_no_prefixo_e_real:
  for n: Nat
  for +xs: List<&2, Quadro>
  for t: Nat
  for -q: Quadro
  for consulta: {consultar(primeiros(n, xs), t) == Some{q} : Maybe<&2, Quadro>}
  {consultar(xs, t) == Some{q} : Maybe<&2, Quadro>}
def consulta_no_prefixo_e_real(n, xs, t, q, consulta):
  match n xs t:
    case 0n _ _: L.ex_falso({consultar(xs, t) == Some{q} : Maybe<&2, Quadro>}, F.nenhum_nao_algum(Quadro, q, consulta))
    case 1n+k Nil{} _: L.ex_falso({consultar(Nil{}, t) == Some{q} : Maybe<&2, Quadro>}, F.nenhum_nao_algum(Quadro, q, consulta))
    case 1n+k Con{h, r} 0n: consulta
    case 1n+k Con{h, r} 1n+u: consulta_no_prefixo_e_real(k, r, u, q, consulta)

law consulta_no_prefixo_respeita_corte:
  for n: Nat
  for xs: List<&2, Quadro>
  for t: Nat
  for -q: Quadro
  for consulta: {consultar(primeiros(n, xs), t) == Some{q} : Maybe<&2, Quadro>}
  {Nat.is_lt(t, n) == True{} : Bool}
def consulta_no_prefixo_respeita_corte(n, xs, t, q, consulta):
  match n xs t:
    case 0n _ _: L.ex_falso({Nat.is_lt(t, 0n) == True{} : Bool}, F.nenhum_nao_algum(Quadro, q, consulta))
    case 1n+k Nil{} _: L.ex_falso({Nat.is_lt(t, 1n+k) == True{} : Bool}, F.nenhum_nao_algum(Quadro, q, consulta))
    case 1n+k Con{h, r} 0n: {==}
    case 1n+k Con{h, r} 1n+u: consulta_no_prefixo_respeita_corte(k, r, u, q, consulta)

law consulta_antes_do_corte_e_conservada:
  for n: Nat
  for xs: List<&2, Quadro>
  for t: Nat
  for menor: {Nat.is_lt(t, n) == True{} : Bool}
  {consultar(primeiros(n, xs), t) == consultar(xs, t) : Maybe<&2, Quadro>}
def consulta_antes_do_corte_e_conservada(n, xs, t, menor):
  match n xs t:
    case 0n _ 0n: F.absurdo_booleano({consultar(primeiros(0n, xs), 0n) == consultar(xs, 0n) : Maybe<&2, Quadro>}, menor)
    case 0n _ 1n+u: F.absurdo_booleano({consultar(primeiros(0n, xs), 1n+u) == consultar(xs, 1n+u) : Maybe<&2, Quadro>}, menor)
    case 1n+k Nil{} _: {==}
    case 1n+k Con{h, r} 0n: {==}
    case 1n+k Con{h, r} 1n+u: consulta_antes_do_corte_e_conservada(k, r, u, menor)
