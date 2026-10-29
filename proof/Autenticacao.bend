# A identidade exigida pelo certificado e derivada do cadastro publicado.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./Ordens.bend as O

def validade_cauda(+h: D.Linha, +t: List<&2, D.Linha>, +e: D.EsquemaTabela,
  v: {D.linhas_validas(Con{h, t}, e) == True{} : Bool}) ->
  L.E<{D.linhas_depois(t, D.linha_chave(h)) == True{} : Bool},
    {D.linhas_validas(t, e) == True{} : Bool}>:
  D.Linha{k, fs} = h
  F.com_par(
    L.E<{D.linhas_depois(t, k) == True{} : Bool}, {D.linhas_validas(t, e) == True{} : Bool}>,
    {D.linha_valida(e, D.Linha{k, fs}) && D.linhas_depois(t, k) == True{} : Bool},
    {D.linhas_validas(t, e) == True{} : Bool},
    F.e_booleano_separar(D.linha_valida(e, D.Linha{k, fs}) && D.linhas_depois(t, k), D.linhas_validas(t, e), v),
    primeiro => cauda => L.Ambos{F.e_booleano_direita(D.linha_valida(e, D.Linha{k, fs}), D.linhas_depois(t, k), primeiro), cauda})

def acima_casos(b: Bool, +k: String, +fs: List<&2, D.Campo>,
  -t: List<&2, D.Linha>, -cred: String, +ctx: D.Contexto, +baixo: String,
  menor: {String.is_lt(baixo, k) == True{} : Bool},
  rec: {D.autenticar_linhas(t, cred) == Some{ctx} : Maybe<&2, D.Contexto>} ->
    {String.is_lt(k, D.contexto_id(ctx)) == True{} : Bool},
  aut: {Bool.pick(Maybe<&2, D.Contexto>, b,
    Some{D.contexto_linha(D.Linha{k, fs})}, D.autenticar_linhas(t, cred)) ==
      Some{ctx} : Maybe<&2, D.Contexto>}) ->
  {String.is_lt(baixo, D.contexto_id(ctx)) == True{} : Bool}:
  match b:
    case False{}:
      O.string_lt_trans(baixo, k, D.contexto_id(ctx), menor, rec(aut))
    case True{}:
      %F.algum_injetivo(D.Contexto, D.contexto_linha(D.Linha{k, fs}), ctx, aut) :
        {String.is_lt(baixo, D.contexto_id(_)) == True{} : Bool}
      menor

law autenticado_acima:
  for xs: List<&2, D.Linha>
  for +e: D.EsquemaTabela
  for +cred: String
  for +ctx: D.Contexto
  for +baixo: String
  for v: {D.linhas_validas(xs, e) == True{} : Bool}
  for d: {D.linhas_depois(xs, baixo) == True{} : Bool}
  for aut: {D.autenticar_linhas(xs, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  {String.is_lt(baixo, D.contexto_id(ctx)) == True{} : Bool}
def autenticado_acima(xs, e, cred, ctx, baixo, v, d, aut):
  match xs:
    case Nil{}:
      L.ex_falso({String.is_lt(baixo, D.contexto_id(ctx)) == True{} : Bool},
        F.nenhum_nao_algum(D.Contexto, ctx, aut))
    case Con{D.Linha{+k, +fs}, +t}:
      F.com_par({String.is_lt(baixo, D.contexto_id(ctx)) == True{} : Bool},
        {D.linhas_depois(t, k) == True{} : Bool}, {D.linhas_validas(t, e) == True{} : Bool},
        validade_cauda(D.Linha{k, fs}, t, e, v),
        dt => vt => acima_casos(String.eq(D.credencial_linha(D.Linha{k, fs}), cred), k, fs, t,
          cred, ctx, baixo, d, h => autenticado_acima(t, e, cred, ctx, k, vt, dt, h), aut))

law contexto_refl:
  for c: D.Contexto
  {D.contexto_igual(c, c) == True{} : Bool}
def contexto_refl(c):
  match c:
    case D.Contexto{id, tipo}:
      F.e_booleano_intro(String.eq(id, id), String.eq(tipo, tipo),
        O.string_eq_refl(id), O.string_eq_refl(tipo))

def presente_casos(b: Bool, +k: String, +fs: List<&2, D.Campo>,
  +t: List<&2, D.Linha>, +cred: String, +ctx: D.Contexto,
  rec: {D.autenticar_linhas(t, cred) == Some{ctx} : Maybe<&2, D.Contexto>} ->
    L.E<{D.contexto_encontrado(D.achar_linha(t, D.contexto_id(ctx)), ctx) == True{} : Bool},
      {String.is_lt(k, D.contexto_id(ctx)) == True{} : Bool}>,
  aut: {Bool.pick(Maybe<&2, D.Contexto>, b,
    Some{D.contexto_linha(D.Linha{k, fs})}, D.autenticar_linhas(t, cred)) ==
      Some{ctx} : Maybe<&2, D.Contexto>}) ->
  {D.contexto_encontrado(D.achar_linha(Con{D.Linha{k, fs}, t}, D.contexto_id(ctx)), ctx) == True{} : Bool}:
  match b:
    case False{}:
      F.com_par(
        {D.contexto_encontrado(D.achar_linha(Con{D.Linha{k, fs}, t}, D.contexto_id(ctx)), ctx) == True{} : Bool},
        {D.contexto_encontrado(D.achar_linha(t, D.contexto_id(ctx)), ctx) == True{} : Bool},
        {String.is_lt(k, D.contexto_id(ctx)) == True{} : Bool}, rec(aut),
        presente => menor =>
          %Equal.sym(Bool, String.eq(k, D.contexto_id(ctx)), False{}, O.string_lt_neq(k, D.contexto_id(ctx), menor)) :
            {D.contexto_encontrado(Bool.pick(Maybe<&2, D.Linha>, _, Some{D.Linha{k, fs}}, D.achar_linha(t, D.contexto_id(ctx))), ctx) == True{} : Bool}
          presente)
    case True{}:
      %F.algum_injetivo(D.Contexto, D.contexto_linha(D.Linha{k, fs}), ctx, aut) :
        {D.contexto_encontrado(D.achar_linha(Con{D.Linha{k, fs}, t}, D.contexto_id(_)), _) == True{} : Bool}
      %Equal.sym(Bool, String.eq(k, k), True{}, O.string_eq_refl(k)) :
        {D.contexto_encontrado(Bool.pick(Maybe<&2, D.Linha>, _, Some{D.Linha{k, fs}},
          D.achar_linha(t, k)), D.contexto_linha(D.Linha{k, fs})) == True{} : Bool}
      contexto_refl(D.contexto_linha(D.Linha{k, fs}))

# A prova geral e declarada antes dos auxiliares que a compoem.
law autenticado_presente:
  for +xs: List<&2, D.Linha>
  for +e: D.EsquemaTabela
  for +cred: String
  for +ctx: D.Contexto
  for +v: {D.linhas_validas(xs, e) == True{} : Bool}
  for +aut: {D.autenticar_linhas(xs, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  {D.contexto_encontrado(D.achar_linha(xs, D.contexto_id(ctx)), ctx) == True{} : Bool}

def autenticado_presente(xs, e, cred, ctx, v, aut):
  match xs:
    case Nil{}:
      L.ex_falso({D.contexto_encontrado(D.achar_linha(Nil{}, D.contexto_id(ctx)), ctx) == True{} : Bool},
        F.nenhum_nao_algum(D.Contexto, ctx, aut))
    case Con{D.Linha{k, fs}, t}:
      F.com_par(
        {D.contexto_encontrado(D.achar_linha(Con{D.Linha{k, fs}, t}, D.contexto_id(ctx)), ctx) == True{} : Bool},
        {D.linhas_depois(t, k) == True{} : Bool}, {D.linhas_validas(t, e) == True{} : Bool},
        validade_cauda(D.Linha{k, fs}, t, e, v),
        dt => +vt => presente_casos(String.eq(D.credencial_linha(D.Linha{k, fs}), cred), k, fs, t, cred, ctx,
          +h => L.Ambos{autenticado_presente(t, e, cred, ctx, vt, h),
            autenticado_acima(t, e, cred, ctx, k, vt, dt, h)}, aut))

law autenticacao_implica_contexto_presente:
  for +e: D.Esquema
  for +s: D.Estado
  for cred: String
  for ctx: D.Contexto
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  for aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  {D.contexto_presente(s, ctx) == True{} : Bool}
def autenticacao_implica_contexto_presente(e, s, cred, ctx, estrutura, aut):
  match e s:
    case D.Esquema{es} D.Estado{ts, us}:
      sem_credenciais = F.e_booleano_esquerda(
        D.tabelas_validas(es, ts) && D.linhas_validas(us, D.esquema_usuarios()),
        D.credenciais_validas(us), estrutura)
      linhas = F.e_booleano_direita(D.tabelas_validas(es, ts),
        D.linhas_validas(us, D.esquema_usuarios()), sem_credenciais)
      autenticado_presente(us, D.esquema_usuarios(), cred, ctx, linhas, aut)

law comparar_com_vazio:
  for s: String
  {String.eq(s, "") == String.is_empty(s) : Bool}
def comparar_com_vazio(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{n}, t}:
      {==}

law cadastro_valido_nao_autentica_vazio:
  for xs: List<&2, D.Linha>
  for +valido: {D.credenciais_validas(xs) == True{} : Bool}
  {D.autenticar_linhas(xs, "") == None{} : Maybe<&2, D.Contexto>}
def cadastro_valido_nao_autentica_vazio(xs, valido):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +cred = D.credencial_linha(h)
      nao_vazia = F.e_booleano_esquerda(Bool.not(String.is_empty(cred)), D.credencial_diferente(t, cred),
        F.e_booleano_esquerda(Bool.not(String.is_empty(cred)) && D.credencial_diferente(t, cred),
          D.credenciais_validas(t), valido))
      cauda = F.e_booleano_direita(Bool.not(String.is_empty(cred)) && D.credencial_diferente(t, cred),
        D.credenciais_validas(t), valido)
      %Equal.sym(Bool, String.eq(cred, ""), False{},
        Equal.trans(Bool, String.eq(cred, ""), String.is_empty(cred), False{},
          comparar_com_vazio(cred), F.negacao_verdadeira(String.is_empty(cred), nao_vazia))) :
          {Bool.pick(Maybe<&2, D.Contexto>, _, Some{D.contexto_linha(h)}, D.autenticar_linhas(t, "")) == None{} : Maybe<&2, D.Contexto>}
      cadastro_valido_nao_autentica_vazio(t, cauda)

law estado_publicavel_nao_autentica_vazio:
  for e: D.Esquema
  for s: D.Estado
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  {D.autenticar(s, "") == None{} : Maybe<&2, D.Contexto>}
def estado_publicavel_nao_autentica_vazio(e, s, estrutura):
  match e s:
    case D.Esquema{es} D.Estado{ts, +us}:
      cadastro_valido_nao_autentica_vazio(us,
        F.e_booleano_direita(D.tabelas_validas(es, ts) && D.linhas_validas(us, D.esquema_usuarios()),
          D.credenciais_validas(us), estrutura))
