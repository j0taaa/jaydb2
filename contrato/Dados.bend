# JayDB: universo de dados e operacoes logicas de referencia.
# Nao contem politicas de permissao; nenhuma operacao deste modulo
# e uma interface publica separada da submissao de codigo e prova.
import Base

type Valor is Data:
  VAusente{}
  VBool{valor: Bool}
  VInt{alto: U32, baixo: U32}
  VTexto{texto: String}
  VListaVazia{}
  VLista{cabeca: Valor, cauda: Valor}
  VRegistroVazio{}
  VRegistro{nome: String, valor: Valor, resto: Valor}

type Tipo is Data:
  Texto{}
  Booleano{}
  Inteiro{}

type Coluna is Data:
  Coluna{nome: String, tipo: Tipo, opcional: Bool}

type EsquemaTabela is Data:
  EsquemaTabela{nome: String, chave: String, colunas: List<&2, Coluna>}

type Esquema is Data:
  Esquema{tabelas: List<&2, EsquemaTabela>}

type Campo is Data:
  Campo{nome: String, valor: Valor}

type Linha is Data:
  Linha{chave: String, campos: List<&2, Campo>}

type Tabela is Data:
  Tabela{nome: String, linhas: List<&2, Linha>}

type Estado is Data:
  Estado{tabelas: List<&2, Tabela>, usuarios: List<&2, Linha>}

type Contexto is Data:
  Contexto{id: String, tipo: String}

type Colecao is Data:
  Usuarios{}
  Aplicacao{nome: String}

type Operacao is Data:
  LerCelula{colecao: Colecao, chave: String, coluna: String}
  VerExistencia{colecao: Colecao, chave: String}
  ContarLinhas{colecao: Colecao}
  EnumerarChaves{colecao: Colecao}
  DefinirLinha{colecao: Colecao, chave: String, campos: List<&2, Campo>}
  DefinirColuna{colecao: Colecao, chave: String, coluna: String, valor: Valor}
  RemoverLinha{colecao: Colecao, chave: String}

type Observacao is Data:
  LinhaAusente{}
  Celula{valor: Valor}
  Existencia{existe: Bool}
  Quantidade{numero: Nat}
  Chaves{chaves: List<&2, String>}

type ResultadoOp is Data:
  FalhaDados{}
  Observado{observacao: Observacao}
  Alterado{estado: Estado}

# U32 e exato; os dois words de VInt representam os 64 bits
# do complemento de dois. Nao ha conversao numerica implicita.
def escalar_valido(+n: U32) -> Bool:
  U32.is_lt(n, 1114112) && (U32.is_lt(n, 55296) || U32.is_ge(n, 57344))

def unicode_valido(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{n}, t}:
      escalar_valido(n) && unicode_valido(t)

def inicio_nome(+c: Char) -> Bool:
  Char.is_alpha(c) || Char.is_eq(c, '_')

def resto_nome(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      (inicio_nome(h) || Char.is_digit(h)) && resto_nome(t)

def nome_valido(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      inicio_nome(h) && resto_nome(t) && Nat.is_le(String.length(s), 64n)

def eh_lista(v: Valor) -> Bool:
  match v:
    case VListaVazia{}:
      True{}
    case VLista{h, t}:
      True{}
    case _:
      False{}

def eh_registro(v: Valor) -> Bool:
  match v:
    case VRegistroVazio{}:
      True{}
    case VRegistro{n, v, r}:
      True{}
    case _:
      False{}

def registro_depois(v: Valor, nome: String) -> Bool:
  match v:
    case VRegistroVazio{}:
      True{}
    case VRegistro{n, x, r}:
      String.is_lt(nome, n)
    case _:
      False{}

def valor_valido(v: Valor) -> Bool:
  match v:
    case VAusente{}:
      True{}
    case VBool{b}:
      True{}
    case VInt{a, b}:
      True{}
    case VTexto{s}:
      unicode_valido(s)
    case VListaVazia{}:
      True{}
    case VLista{h, +t}:
      valor_valido(h) && eh_lista(t) && valor_valido(t)
    case VRegistroVazio{}:
      True{}
    case VRegistro{+n, v, +r}:
      nome_valido(n) && valor_valido(v) && registro_depois(r, n) && valor_valido(r)

def valor_tipo(t: Tipo, v: Valor) -> Bool:
  match t v:
    case Texto{} VTexto{s}:
      unicode_valido(s)
    case Booleano{} VBool{b}:
      True{}
    case Inteiro{} VInt{a, b}:
      True{}
    case _ _:
      False{}

def cabe_coluna(v: Valor, t: Tipo, opcional: Bool) -> Bool:
  match v:
    case VAusente{}:
      opcional
    case _:
      valor_tipo(t, v)

def coluna_nome(c: Coluna) -> String:
  Coluna{n, t, o} = c
  n

def campo_nome(c: Campo) -> String:
  Campo{n, v} = c
  n

def achar_coluna(xs: List<&2, Coluna>, +nome: String) -> Maybe<&2, Coluna>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Bool.pick(Maybe<&2, Coluna>, String.eq(coluna_nome(h), nome), Some{h}, achar_coluna(t, nome))

def achar_campo(xs: List<&2, Campo>, +nome: String) -> Maybe<&2, Valor>:
  match xs:
    case Nil{}:
      None{}
    case Con{Campo{n, v}, t}:
      Bool.pick(Maybe<&2, Valor>, String.eq(n, nome), Some{v}, achar_campo(t, nome))

def achar_linha(xs: List<&2, Linha>, +chave: String) -> Maybe<&2, Linha>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Linha{k, fs} = h
      Bool.pick(Maybe<&2, Linha>, String.eq(k, chave), Some{h}, achar_linha(t, chave))

def achar_esquema(xs: List<&2, EsquemaTabela>, +nome: String) -> Maybe<&2, EsquemaTabela>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      EsquemaTabela{n, k, cs} = h
      Bool.pick(Maybe<&2, EsquemaTabela>, String.eq(n, nome), Some{h}, achar_esquema(t, nome))

def achar_tabela(xs: List<&2, Tabela>, +nome: String) -> Maybe<&2, Tabela>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Tabela{n, ls} = h
      Bool.pick(Maybe<&2, Tabela>, String.eq(n, nome), Some{h}, achar_tabela(t, nome))

def esquema_usuarios() -> EsquemaTabela:
  EsquemaTabela{"usuarios", "id", [Coluna{"credencial", Texto{}, False{}}, Coluna{"id", Texto{}, False{}}, Coluna{"tipo", Texto{}, False{}}]}

def esquema_colecao(c: Colecao, e: Esquema) -> Maybe<&2, EsquemaTabela>:
  match c:
    case Usuarios{}:
      Some{esquema_usuarios()}
    case Aplicacao{n}:
      Esquema{ts} = e
      achar_esquema(ts, n)

def linhas_tabela(m: Maybe<&2, Tabela>) -> Maybe<&2, List<&2, Linha>>:
  match m:
    case None{}:
      None{}
    case Some{Tabela{n, ls}}:
      Some{ls}

def linhas_colecao(c: Colecao, s: Estado) -> Maybe<&2, List<&2, Linha>>:
  match c:
    case Usuarios{}:
      Estado{ts, us} = s
      Some{us}
    case Aplicacao{n}:
      Estado{ts, us} = s
      linhas_tabela(achar_tabela(ts, n))

# Colunas, campos, tabelas e linhas usam ordem canonica estrita.
# Essa e a representacao matematica; a memoria pode usar outra ordem.
def colunas_depois(xs: List<&2, Coluna>, nome: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      String.is_lt(nome, coluna_nome(h))

def colunas_validas(xs: List<&2, Coluna>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Coluna{+n, t, o}, +r}:
      nome_valido(n) && colunas_depois(r, n) && colunas_validas(r)

def chave_coluna(c: Maybe<&2, Coluna>) -> Bool:
  match c:
    case Some{Coluna{n, Texto{}, False{}}}:
      True{}
    case _:
      False{}

def esquema_tabela_valido(e: EsquemaTabela) -> Bool:
  EsquemaTabela{n, k, +cs} = e
  nome_valido(n) && colunas_validas(cs) && chave_coluna(achar_coluna(cs, k))

def esquemas_depois(xs: List<&2, EsquemaTabela>, nome: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{EsquemaTabela{n, k, cs}, t}:
      String.is_lt(nome, n)

def esquemas_validos(xs: List<&2, EsquemaTabela>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      EsquemaTabela{n, k, cs} = h
      esquema_tabela_valido(h) && esquemas_depois(t, n) && esquemas_validos(t)

def esquema_valido(e: Esquema) -> Bool:
  Esquema{ts} = e
  esquemas_validos(ts)

def campos_validos(cs: List<&2, Coluna>, fs: List<&2, Campo>) -> Bool:
  match cs fs:
    case Nil{} Nil{}:
      True{}
    case Con{Coluna{cn, ct, co}, cr} Con{Campo{fn, fv}, fr}:
      String.eq(cn, fn) && cabe_coluna(fv, ct, co) && campos_validos(cr, fr)
    case _ _:
      False{}

def chave_correta(v: Maybe<&2, Valor>, chave: String) -> Bool:
  match v:
    case Some{VTexto{s}}:
      String.eq(s, chave)
    case _:
      False{}

def linha_valida(e: EsquemaTabela, l: Linha) -> Bool:
  EsquemaTabela{n, k, cs} = e
  Linha{+id, +fs} = l
  unicode_valido(id) && campos_validos(cs, fs) && chave_correta(achar_campo(fs, k), id)

def linhas_depois(xs: List<&2, Linha>, chave: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Linha{k, fs}, t}:
      String.is_lt(chave, k)

def linhas_validas(xs: List<&2, Linha>, +e: EsquemaTabela) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Linha{k, fs} = h
      linha_valida(e, h) && linhas_depois(t, k) && linhas_validas(t, e)

def esquema_nome(e: EsquemaTabela) -> String:
  EsquemaTabela{n, k, cs} = e
  n

def tabelas_validas(es: List<&2, EsquemaTabela>, ts: List<&2, Tabela>) -> Bool:
  match es ts:
    case Nil{} Nil{}:
      True{}
    case Con{+e, er} Con{Tabela{n, ls}, tr}:
      String.eq(esquema_nome(e), n) && linhas_validas(ls, e) && tabelas_validas(er, tr)
    case _ _:
      False{}

def texto_campo(v: Maybe<&2, Valor>) -> String:
  match v:
    case Some{VTexto{s}}:
      s
    case _:
      ""

def credencial_linha(l: Linha) -> String:
  Linha{k, fs} = l
  texto_campo(achar_campo(fs, "credencial"))

def credencial_diferente(xs: List<&2, Linha>, +cred: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.not(String.eq(credencial_linha(h), cred)) && credencial_diferente(t, cred)

def credenciais_validas(xs: List<&2, Linha>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, +t}:
      +cred = credencial_linha(h)
      Bool.not(String.is_empty(cred)) && credencial_diferente(t, cred) && credenciais_validas(t)

def estrutura(e: Esquema, s: Estado) -> Bool:
  Esquema{es} = e
  Estado{ts, +us} = s
  tabelas_validas(es, ts) && linhas_validas(us, esquema_usuarios()) && credenciais_validas(us)

# Autenticacao considera exclusivamente o cadastro publicado de entrada.
def contexto_linha(l: Linha) -> Contexto:
  Linha{id, fs} = l
  Contexto{id, texto_campo(achar_campo(fs, "tipo"))}

def autenticar_linhas(xs: List<&2, Linha>, +credencial: String) -> Maybe<&2, Contexto>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Bool.pick(Maybe<&2, Contexto>, String.eq(credencial_linha(h), credencial), Some{contexto_linha(h)}, autenticar_linhas(t, credencial))

def autenticar(s: Estado, credencial: String) -> Maybe<&2, Contexto>:
  Estado{ts, us} = s
  autenticar_linhas(us, credencial)

# A prova universal fixa a identidade autenticada, sem fixar a credencial.
# Este predicado exige usuario com aquele id e tipo no estado inicial.
def contexto_id(c: Contexto) -> String:
  Contexto{id, tipo} = c
  id

def contexto_igual(a: Contexto, b: Contexto) -> Bool:
  Contexto{ai, at} = a
  Contexto{bi, bt} = b
  String.eq(ai, bi) && String.eq(at, bt)

def contexto_encontrado(m: Maybe<&2, Linha>, c: Contexto) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{l}:
      contexto_igual(contexto_linha(l), c)

def contexto_presente(s: Estado, +c: Contexto) -> Bool:
  Estado{ts, us} = s
  contexto_encontrado(achar_linha(us, contexto_id(c)), c)

# Atualizacoes cegas preservam os campos que nao foram substituidos.
def linha_chave(l: Linha) -> String:
  Linha{k, fs} = l
  k

def inserir_linha(xs: List<&2, Linha>, +nova: Linha) -> List<&2, Linha>:
  match xs:
    case Nil{}:
      [nova]
    case Con{+h, +t}:
      Bool.pick(List<&2, Linha>, String.is_lt(linha_chave(nova), linha_chave(h)), nova <> h <> t,
        Bool.pick(List<&2, Linha>, String.eq(linha_chave(nova), linha_chave(h)), nova <> t, h <> inserir_linha(t, nova)))

def retirar_linha(xs: List<&2, Linha>, +chave: String) -> List<&2, Linha>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +resto = retirar_linha(t, chave)
      Bool.pick(List<&2, Linha>, String.eq(linha_chave(h), chave), resto, h <> resto)

def substituir_campo(xs: List<&2, Campo>, +nome: String, +valor: Valor) -> List<&2, Campo>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Bool.pick(Campo, String.eq(campo_nome(h), nome), Campo{nome, valor}, h) <> substituir_campo(t, nome, valor)

def substituir_na_linha(l: Linha, nome: String, valor: Valor) -> Linha:
  Linha{k, fs} = l
  Linha{k, substituir_campo(fs, nome, valor)}

def substituir_coluna(xs: List<&2, Linha>, +chave: String, +nome: String, +valor: Valor) -> List<&2, Linha>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Bool.pick(Linha, String.eq(linha_chave(h), chave), substituir_na_linha(h, nome, valor), h) <> substituir_coluna(t, chave, nome, valor)

def trocar_tabela(xs: List<&2, Tabela>, +nome: String, +linhas: List<&2, Linha>) -> List<&2, Tabela>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Tabela{+n, ls}, t}:
      Bool.pick(Tabela, String.eq(n, nome), Tabela{n, linhas}, Tabela{n, ls}) <> trocar_tabela(t, nome, linhas)

def trocar_colecao(c: Colecao, s: Estado, linhas: List<&2, Linha>) -> Estado:
  match c:
    case Usuarios{}:
      Estado{ts, us} = s
      Estado{ts, linhas}
    case Aplicacao{nome}:
      Estado{ts, us} = s
      Estado{trocar_tabela(ts, nome, linhas), us}

def chaves_linhas(xs: List<&2, Linha>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Linha{k, fs}, t}:
      k <> chaves_linhas(t)

def existe_linha(m: Maybe<&2, Linha>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{l}:
      True{}

def resultado_celula(v: Maybe<&2, Valor>) -> ResultadoOp:
  match v:
    case None{}:
      FalhaDados{}
    case Some{x}:
      Observado{Celula{x}}

def ler_linha(m: Maybe<&2, Linha>, coluna: String) -> ResultadoOp:
  match m:
    case None{}:
      Observado{LinhaAusente{}}
    case Some{Linha{k, fs}}:
      resultado_celula(achar_campo(fs, coluna))

def ler_coluna(c: Maybe<&2, Coluna>, l: Maybe<&2, Linha>, nome: String) -> ResultadoOp:
  match c:
    case None{}:
      FalhaDados{}
    case Some{x}:
      ler_linha(l, nome)

def coluna_escrita_valida(c: Maybe<&2, Coluna>, +primaria: String, +chave: String, +v: Valor) -> Bool:
  match c:
    case None{}:
      False{}
    case Some{Coluna{nome, t, o}}:
      cabe_coluna(v, t, o) && (Bool.not(String.eq(nome, primaria)) || chave_correta(Some{v}, chave))

def escrever_se(ok: Bool, c: Colecao, s: Estado, linhas: List<&2, Linha>) -> ResultadoOp:
  match ok:
    case False{}:
      FalhaDados{}
    case True{}:
      Alterado{trocar_colecao(c, s, linhas)}

type Resolvida is Data:
  Resolvida{esquema: EsquemaTabela, linhas: List<&2, Linha>}

def resolver_partes(e: Maybe<&2, EsquemaTabela>, ls: Maybe<&2, List<&2, Linha>>) -> Maybe<&2, Resolvida>:
  match e ls:
    case Some{x} Some{ys}:
      Some{Resolvida{x, ys}}
    case _ _:
      None{}

def colecao_op(o: Operacao) -> Colecao:
  match o:
    case LerCelula{c, k, n}:
      c
    case VerExistencia{c, k}:
      c
    case ContarLinhas{c}:
      c
    case EnumerarChaves{c}:
      c
    case DefinirLinha{c, k, fs}:
      c
    case DefinirColuna{c, k, n, v}:
      c
    case RemoverLinha{c, k}:
      c

def operar_resolvida(o: Operacao, r: Maybe<&2, Resolvida>, s: Estado) -> ResultadoOp:
  match o r:
    case LerCelula{c, k, +n} Some{Resolvida{EsquemaTabela{en, pk, cs}, ls}}:
      ler_coluna(achar_coluna(cs, n), achar_linha(ls, k), n)
    case VerExistencia{c, k} Some{Resolvida{e, ls}}:
      Observado{Existencia{existe_linha(achar_linha(ls, k))}}
    case ContarLinhas{c} Some{Resolvida{e, ls}}:
      Observado{Quantidade{List.length(&2, Linha, ls)}}
    case EnumerarChaves{c} Some{Resolvida{e, ls}}:
      Observado{Chaves{chaves_linhas(ls)}}
    case DefinirLinha{c, +k, +fs} Some{Resolvida{e, ls}}:
      escrever_se(linha_valida(e, Linha{k, fs}), c, s, inserir_linha(ls, Linha{k, fs}))
    case DefinirColuna{c, +k, +n, +v} Some{Resolvida{EsquemaTabela{en, pk, cs}, ls}}:
      escrever_se(coluna_escrita_valida(achar_coluna(cs, n), pk, k, v), c, s, substituir_coluna(ls, k, n, v))
    case RemoverLinha{c, k} Some{Resolvida{e, ls}}:
      Alterado{trocar_colecao(c, s, retirar_linha(ls, k))}
    case _ _:
      FalhaDados{}

# Uma chave calculada pelo programa tambem precisa ser Unicode valido.
# A recusa desta chave depende do argumento, nunca da existencia da linha.
def endereco_op_valido(o: Operacao) -> Bool:
  match o:
    case LerCelula{c, k, n}:
      unicode_valido(k)
    case VerExistencia{c, k}:
      unicode_valido(k)
    case ContarLinhas{c}:
      True{}
    case EnumerarChaves{c}:
      True{}
    case DefinirLinha{c, k, fs}:
      unicode_valido(k)
    case DefinirColuna{c, k, n, v}:
      unicode_valido(k)
    case RemoverLinha{c, k}:
      unicode_valido(k)

def operar_endereco(ok: Bool, e: Esquema, +s: Estado, +o: Operacao) -> ResultadoOp:
  match ok:
    case False{}:
      FalhaDados{}
    case True{}:
      +c = colecao_op(o)
      operar_resolvida(o, resolver_partes(esquema_colecao(c, e), linhas_colecao(c, s)), s)

# Uma escrita nao devolve booleanos de existencia nem os valores antigos.
# A validacao do endereco e do valor novo precede qualquer efeito.
def operar(e: Esquema, s: Estado, +o: Operacao) -> ResultadoOp:
  operar_endereco(endereco_op_valido(o), e, s, o)

# Forma canonica usada para medir/publicar o estado; nao exige esta
# representacao em memoria. Uma Linha guarda sua chave duas vezes
# somente no modelo; o valor canonico guarda os campos uma unica vez.
def campos_valor(xs: List<&2, Campo>) -> Valor:
  match xs:
    case Nil{}:
      VRegistroVazio{}
    case Con{Campo{n, v}, t}:
      VRegistro{n, v, campos_valor(t)}

def linhas_valor(xs: List<&2, Linha>) -> Valor:
  match xs:
    case Nil{}:
      VListaVazia{}
    case Con{Linha{k, fs}, t}:
      VLista{campos_valor(fs), linhas_valor(t)}

def tabelas_valor(xs: List<&2, Tabela>) -> Valor:
  match xs:
    case Nil{}:
      VListaVazia{}
    case Con{Tabela{n, ls}, t}:
      VLista{VRegistro{"linhas", linhas_valor(ls), VRegistro{"nome", VTexto{n}, VRegistroVazio{}}}, tabelas_valor(t)}

def estado_valor(s: Estado) -> Valor:
  Estado{ts, us} = s
  VRegistro{"tabelas", tabelas_valor(ts), VRegistro{"usuarios", linhas_valor(us), VRegistroVazio{}}}
