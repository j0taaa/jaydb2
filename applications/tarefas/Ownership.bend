# Preservacao da propriedade das tarefas pelas operacoes autorizadas.
import Base
import ./Dados.bend as D
import ./Logica.bend as L
import ./Policy.bend as Policy
import ./Ordens.bend as O

def Conserva(+ctx: D.Contexto, r: D.ResultadoOp) -> Type:
  match r:
    case D.FalhaDados{}: Unit
    case D.Observado{o}: Unit
    case D.Alterado{w}:
      L.E<Policy.Donos(w), {D.contexto_presente(w, ctx) == True{} : Bool}>

def impossivel(-A: Type, h: {False{} == True{} : Bool}) -> A:
  L.ex_falso(A, (%h : Bool.pick(Type, _, Empty, Unit) Unit{}))

def presente_existe(m: Maybe<&2, D.Linha>, -ctx: D.Contexto,
  h: {D.contexto_encontrado(m, ctx) == True{} : Bool}) ->
  {D.existe_linha(m) == True{} : Bool}:
  match m:
    case None{}:
      impossivel({False{} == True{} : Bool}, h)
    case Some{l}:
      {==}

def inserir_passo(a: Bool, b: Bool, +us: List<&2, D.Linha>, +nome: String,
  +nova: D.Linha, +l: D.Linha, +ls: List<&2, D.Linha>,
  hn: Policy.Dono(us, nome, nova), hl: Policy.Dono(us, nome, l),
  ht: Policy.Linhas(us, nome, ls),
  hr: Policy.Linhas(us, nome, D.inserir_linha(ls, nova))) ->
  Policy.Linhas(us, nome, Bool.pick(List<&2, D.Linha>, a, nova <> l <> ls,
    Bool.pick(List<&2, D.Linha>, b, nova <> ls, l <> D.inserir_linha(ls, nova)))):
  match a b:
    case True{} _:
      Policy.Ambos{hn, Policy.Ambos{hl, ht}}
    case False{} True{}:
      Policy.Ambos{hn, ht}
    case False{} False{}:
      Policy.Ambos{hl, hr}

def inserir_preserva(+us: List<&2, D.Linha>, +nome: String,
  ls: List<&2, D.Linha>, +nova: D.Linha,
  +hn: Policy.Dono(us, nome, nova), h: Policy.Linhas(us, nome, ls)) ->
  Policy.Linhas(us, nome, D.inserir_linha(ls, nova)):
  match ls:
    case Nil{}:
      Policy.Ambos{hn, Unit{}}
    case Con{+l, +resto}:
      Policy.Ambos{+hl, +ht} = h
      inserir_passo(String.is_lt(D.linha_chave(nova), D.linha_chave(l)),
        String.eq(D.linha_chave(nova), D.linha_chave(l)), us, nome, nova, l, resto,
        hn, hl, ht, inserir_preserva(us, nome, resto, nova, hn, ht))

def retirar_passo(b: Bool, +us: List<&2, D.Linha>, +nome: String,
  +l: D.Linha, +ls: List<&2, D.Linha>,
  hl: Policy.Dono(us, nome, l), ht: Policy.Linhas(us, nome, ls)) ->
  Policy.Linhas(us, nome, Bool.pick(List<&2, D.Linha>, b, ls, l <> ls)):
  match b:
    case False{}: Policy.Ambos{hl, ht}
    case True{}: ht

def retirar_preserva(+us: List<&2, D.Linha>, +nome: String,
  ls: List<&2, D.Linha>, +chave: String, h: Policy.Linhas(us, nome, ls)) ->
  Policy.Linhas(us, nome, D.retirar_linha(ls, chave)):
  match ls:
    case Nil{}: Unit{}
    case Con{+l, +resto}:
      Policy.Ambos{hl, ht} = h
      retirar_passo(String.eq(D.linha_chave(l), chave), us, nome, l,
        D.retirar_linha(resto, chave), hl, retirar_preserva(us, nome, resto, chave, ht))

def trocar_passo(b: Bool, +us: List<&2, D.Linha>, +n: String, +nome: String,
  +ls: List<&2, D.Linha>, +novas: List<&2, D.Linha>, +resto: List<&2, D.Tabela>,
  eq: {String.eq(n, nome) == b : Bool}, hl: Policy.Linhas(us, n, ls),
  hn: Policy.Linhas(us, nome, novas), ht: Policy.Tabelas(us, resto)) ->
  Policy.Tabelas(us, Bool.pick(D.Tabela, b, D.Tabela{n, novas}, D.Tabela{n, ls}) <> resto):
  match b:
    case False{}:
      Policy.Ambos{hl, ht}
    case True{}:
      Policy.Ambos{(%Equal.sym(String, n, nome, O.string_igual(n, nome, eq)) :
        Policy.Linhas(us, _, novas) hn), ht}

def trocar_preserva(+us: List<&2, D.Linha>, ts: List<&2, D.Tabela>,
  +nome: String, +novas: List<&2, D.Linha>,
  +hn: Policy.Linhas(us, nome, novas), h: Policy.Tabelas(us, ts)) ->
  Policy.Tabelas(us, D.trocar_tabela(ts, nome, novas)):
  match ts:
    case Nil{}: Unit{}
    case Con{D.Tabela{+n, +ls}, +resto}:
      Policy.Ambos{hl, ht} = h
      trocar_passo(String.eq(n, nome), us, n, nome, ls, novas,
        D.trocar_tabela(resto, nome, novas), {==}, hl, hn,
        trocar_preserva(us, resto, nome, novas, hn, ht))

def Achadas(+us: List<&2, D.Linha>, +nome: String,
  m: Maybe<&2, List<&2, D.Linha>>) -> Data:
  match m:
    case None{}: Unit
    case Some{ls}: Policy.Linhas(us, nome, ls)

def achar_passo(b: Bool, +us: List<&2, D.Linha>, +n: String, +nome: String,
  +ls: List<&2, D.Linha>, +resto: Maybe<&2, D.Tabela>,
  eq: {String.eq(n, nome) == b : Bool}, hl: Policy.Linhas(us, n, ls),
  ht: Achadas(us, nome, D.linhas_tabela(resto))) ->
  Achadas(us, nome, D.linhas_tabela(Bool.pick(Maybe<&2, D.Tabela>, b,
    Some{D.Tabela{n, ls}}, resto))):
  match b:
    case False{}: ht
    case True{}:
      %O.string_igual(n, nome, eq) : Policy.Linhas(us, _, ls)
      hl

def achar_preserva(+us: List<&2, D.Linha>, ts: List<&2, D.Tabela>,
  +nome: String, h: Policy.Tabelas(us, ts)) ->
  Achadas(us, nome, D.linhas_tabela(D.achar_tabela(ts, nome))):
  match ts:
    case Nil{}: Unit{}
    case Con{D.Tabela{+n, +ls}, +resto}:
      Policy.Ambos{hl, ht} = h
      achar_passo(String.eq(n, nome), us, n, nome, ls, D.achar_tabela(resto, nome),
        {==}, hl, achar_preserva(us, resto, nome, ht))

def usuarios(s: D.Estado) -> List<&2, D.Linha>:
  D.Estado{ts, us} = s
  us

def colecao_preserva(+ctx: D.Contexto, +s: D.Estado, +nome: String,
  +ls: List<&2, D.Linha>, h: Policy.Donos(s), hn: Policy.Linhas(usuarios(s), nome, ls),
  aut: {D.contexto_presente(s, ctx) == True{} : Bool}) ->
  Conserva(ctx, D.Alterado{D.trocar_colecao(D.Aplicacao{nome}, s, ls)}):
  D.Estado{ts, us} = s
  L.Ambos{trocar_preserva(us, ts, nome, ls, hn, h), aut}

def escrita_preserva(ok: Bool, +ctx: D.Contexto, +s: D.Estado, +nome: String,
  +ls: List<&2, D.Linha>, h: Policy.Donos(s), hn: Policy.Linhas(usuarios(s), nome, ls),
  aut: {D.contexto_presente(s, ctx) == True{} : Bool}) ->
  Conserva(ctx, D.escrever_se(ok, D.Aplicacao{nome}, s, ls)):
  match ok:
    case False{}: Unit{}
    case True{}: colecao_preserva(ctx, s, nome, ls, h, hn, aut)

def celula_preserva(+ctx: D.Contexto, v: Maybe<&2, D.Valor>) ->
  Conserva(ctx, D.resultado_celula(v)):
  match v:
    case None{}: Unit{}
    case Some{x}: Unit{}

def ler_linha_preserva(+ctx: D.Contexto, m: Maybe<&2, D.Linha>, +nome: String) ->
  Conserva(ctx, D.ler_linha(m, nome)):
  match m:
    case None{}: Unit{}
    case Some{D.Linha{k, fs}}: celula_preserva(ctx, D.achar_campo(fs, nome))

def ler_preserva(+ctx: D.Contexto, c: Maybe<&2, D.Coluna>,
  +m: Maybe<&2, D.Linha>, +nome: String) -> Conserva(ctx, D.ler_coluna(c, m, nome)):
  match c:
    case None{}: Unit{}
    case Some{x}: ler_linha_preserva(ctx, m, nome)

def Resolvidas(+us: List<&2, D.Linha>, +nome: String,
  r: Maybe<&2, D.Resolvida>) -> Data:
  match r:
    case None{}: Unit
    case Some{D.Resolvida{e, ls}}: Policy.Linhas(us, nome, ls)

def resolver_preserva(+us: List<&2, D.Linha>, +nome: String,
  e: Maybe<&2, D.EsquemaTabela>, ls: Maybe<&2, List<&2, D.Linha>>,
  h: Achadas(us, nome, ls)) -> Resolvidas(us, nome, D.resolver_partes(e, ls)):
  match e ls:
    case Some{x} Some{ys}: h
    case Some{x} None{}: Unit{}
    case None{} _: Unit{}

def linhas_resolvidas(+s: D.Estado, +e: D.Esquema, +nome: String,
  h: Policy.Donos(s)) ->
  Resolvidas(usuarios(s), nome, D.resolver_partes(
    D.esquema_colecao(D.Aplicacao{nome}, e), D.linhas_colecao(D.Aplicacao{nome}, s))):
  D.Estado{ts, us} = s
  resolver_preserva(us, nome, D.esquema_colecao(D.Aplicacao{nome}, e),
    D.linhas_tabela(D.achar_tabela(ts, nome)), achar_preserva(us, ts, nome, h))

def nova_dona(+s: D.Estado, +ctx: D.Contexto, +nome: String,
  +k: String, +fs: List<&2, D.Campo>,
  aut: {D.contexto_presente(s, ctx) == True{} : Bool},
  p: Policy.Permitida(ctx, D.DefinirLinha{D.Aplicacao{nome}, k, fs})) ->
  Policy.Dono(usuarios(s), nome, D.Linha{k, fs}):
  D.Estado{ts, us} = s
  D.Contexto{+id, +tipo} = ctx
  Policy.Ambos{eq, dono} = p
  %Equal.sym(String, nome, id, eq) : Policy.Dono(us, _, D.Linha{k, fs})
  Policy.Ambos{dono, presente_existe(D.achar_linha(us, id), D.Contexto{id, tipo}, aut)}

def Resolucao(+s: D.Estado, c: D.Colecao,
  r: Maybe<&2, D.Resolvida>) -> Data:
  match c:
    case D.Usuarios{}: Unit
    case D.Aplicacao{nome}: Resolvidas(usuarios(s), nome, r)

def proibida(-ctx: D.Contexto, -r: D.ResultadoOp,
  p: {False{} == True{} : Bool}) -> Conserva(ctx, r):
  impossivel(Conserva(ctx, r), p)

def resolvida_preserva(+s: D.Estado, +ctx: D.Contexto, op: D.Operacao,
  r: Maybe<&2, D.Resolvida>, +h: Policy.Donos(s),
  +aut: {D.contexto_presente(s, ctx) == True{} : Bool},
  p: Policy.Permitida(ctx, op), hr: Resolucao(s, D.colecao_op(op), r)) ->
  Conserva(ctx, D.operar_resolvida(op, r, s)):
  D.Contexto{+id, +tipo} = ctx
  match op r:
    case D.LerCelula{D.Aplicacao{nome}, k, +n} Some{D.Resolvida{D.EsquemaTabela{en, pk, cs}, ls}}:
      ler_preserva(D.Contexto{id, tipo}, D.achar_coluna(cs, n), D.achar_linha(ls, k), n)
    case D.VerExistencia{D.Aplicacao{nome}, k} Some{D.Resolvida{e, ls}}: Unit{}
    case D.ContarLinhas{D.Aplicacao{nome}} Some{D.Resolvida{e, ls}}: Unit{}
    case D.EnumerarChaves{D.Aplicacao{nome}} Some{D.Resolvida{e, ls}}: Unit{}
    case D.DefinirLinha{D.Aplicacao{+nome}, +k, +fs} Some{D.Resolvida{+e, +ls}}:
      escrita_preserva(D.linha_valida(e, D.Linha{k, fs}), D.Contexto{id, tipo}, s, nome,
        D.inserir_linha(ls, D.Linha{k, fs}), h,
        inserir_preserva(usuarios(s), nome, ls, D.Linha{k, fs},
          nova_dona(s, D.Contexto{id, tipo}, nome, k, fs, aut, p), hr), aut)
    case D.RemoverLinha{D.Aplicacao{+nome}, +k} Some{D.Resolvida{e, +ls}}:
      colecao_preserva(D.Contexto{id, tipo}, s, nome, D.retirar_linha(ls, k), h,
        retirar_preserva(usuarios(s), nome, ls, k, hr), aut)
    case D.LerCelula{D.Usuarios{}, k, n} Some{rr}:
      proibida(D.Contexto{id, tipo}, D.operar_resolvida(D.LerCelula{D.Usuarios{}, k, n}, Some{rr}, s), p)
    case D.VerExistencia{D.Usuarios{}, k} Some{rr}:
      proibida(D.Contexto{id, tipo}, D.operar_resolvida(D.VerExistencia{D.Usuarios{}, k}, Some{rr}, s), p)
    case D.ContarLinhas{D.Usuarios{}} Some{rr}:
      proibida(D.Contexto{id, tipo}, D.operar_resolvida(D.ContarLinhas{D.Usuarios{}}, Some{rr}, s), p)
    case D.EnumerarChaves{D.Usuarios{}} Some{rr}:
      proibida(D.Contexto{id, tipo}, D.operar_resolvida(D.EnumerarChaves{D.Usuarios{}}, Some{rr}, s), p)
    case D.DefinirLinha{D.Usuarios{}, k, fs} Some{rr}:
      proibida(D.Contexto{id, tipo}, D.operar_resolvida(D.DefinirLinha{D.Usuarios{}, k, fs}, Some{rr}, s), p)
    case D.RemoverLinha{D.Usuarios{}, k} Some{rr}:
      proibida(D.Contexto{id, tipo}, D.operar_resolvida(D.RemoverLinha{D.Usuarios{}, k}, Some{rr}, s), p)
    case D.DefinirColuna{c, k, n, v} Some{rr}:
      proibida(D.Contexto{id, tipo}, D.operar_resolvida(D.DefinirColuna{c, k, n, v}, Some{rr}, s), p)
    case _ None{}: Unit{}

def resolucao_preserva(+s: D.Estado, +e: D.Esquema,
  +c: D.Colecao, h: Policy.Donos(s)) ->
  Resolucao(s, c, D.resolver_partes(D.esquema_colecao(c, e), D.linhas_colecao(c, s))):
  match c:
    case D.Usuarios{}: Unit{}
    case D.Aplicacao{nome}: linhas_resolvidas(s, e, nome, h)

def endereco_preserva(ok: Bool, +e: D.Esquema, +s: D.Estado,
  +ctx: D.Contexto, +op: D.Operacao, +h: Policy.Donos(s),
  aut: {D.contexto_presente(s, ctx) == True{} : Bool}, p: Policy.Permitida(ctx, op)) ->
  Conserva(ctx, D.operar_endereco(ok, e, s, op)):
  match ok:
    case False{}: Unit{}
    case True{}:
      resolvida_preserva(s, ctx, op, D.resolver_partes(D.esquema_colecao(D.colecao_op(op), e),
        D.linhas_colecao(D.colecao_op(op), s)), h, aut, p, resolucao_preserva(s, e, D.colecao_op(op), h))

law operacao_preserva:
  for +e: D.Esquema
  for +s: D.Estado
  for +ctx: D.Contexto
  for +op: D.Operacao
  for +h: Policy.Donos(s)
  for aut: {D.contexto_presente(s, ctx) == True{} : Bool}
  for p: Policy.Permitida(ctx, op)
  Conserva(ctx, D.operar(e, s, op))
def operacao_preserva(e, s, ctx, op, h, aut, p):
  endereco_preserva(D.endereco_op_valido(op), e, s, ctx, op, h, aut, p)
