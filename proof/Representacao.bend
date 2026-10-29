# Ida e volta da representacao PRIVADA de Estado, usando src/Estado real.
# Esta prova nao e a soundness do parser de bytes de src/Codec.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Estado.bend as E
import ../src/Requisicao.bend as Q
import ../contrato/Protocolo.bend as P
import ./Fundamentos.bend as F
import ./Ordens.bend as O

law campos_reconstroem:
  for fs: List<&2, D.Campo>
  {E.campos(D.campos_valor(fs)) == Some{fs} : Maybe<&2, List<&2, D.Campo>>}
def campos_reconstroem(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{D.Campo{nome, valor}, t}:
      %Equal.sym(Maybe<&2, List<&2, D.Campo>>, E.campos(D.campos_valor(t)), Some{t},
        campos_reconstroem(t)) :
        {E.campos_cons(nome, valor, _) == Some{Con{D.Campo{nome, valor}, t}} : Maybe<&2, List<&2, D.Campo>>}
      {==}

def chave_textual_reconstroi(v: D.Valor, +k: String, -fs: List<&2, D.Campo>,
  correta: {D.chave_correta(Some{v}, k) == True{} : Bool}) ->
  {E.linha_chave(Some{v}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}:
  match v:
    case D.VTexto{s}:
      %O.string_igual(s, k, correta) : {Some{D.Linha{s, fs}} == Some{D.Linha{_, fs}} : Maybe<&2, D.Linha>}
      {==}
    case D.VAusente{}:
      F.absurdo_booleano({E.linha_chave(Some{D.VAusente{}}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)
    case D.VBool{b}:
      F.absurdo_booleano({E.linha_chave(Some{D.VBool{b}}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)
    case D.VInt{a, b}:
      F.absurdo_booleano({E.linha_chave(Some{D.VInt{a, b}}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)
    case D.VListaVazia{}:
      F.absurdo_booleano({E.linha_chave(Some{D.VListaVazia{}}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)
    case D.VLista{h, t}:
      F.absurdo_booleano({E.linha_chave(Some{D.VLista{h, t}}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)
    case D.VRegistroVazio{}:
      F.absurdo_booleano({E.linha_chave(Some{D.VRegistroVazio{}}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)
    case D.VRegistro{n, x, r}:
      F.absurdo_booleano({E.linha_chave(Some{D.VRegistro{n, x, r}}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)

def chave_reconstroi(v: Maybe<&2, D.Valor>, k: String, -fs: List<&2, D.Campo>,
  correta: {D.chave_correta(v, k) == True{} : Bool}) ->
  {E.linha_chave(v, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}:
  match v:
    case None{}:
      F.absurdo_booleano({E.linha_chave(None{}, fs) == Some{D.Linha{k, fs}} : Maybe<&2, D.Linha>}, correta)
    case Some{x}:
      chave_textual_reconstroi(x, k, fs, correta)

law linha_reconstroi:
  for e: D.EsquemaTabela
  for +linha: D.Linha
  for valida: {D.linha_valida(e, linha) == True{} : Bool}
  {E.linha_campos(E.campos(D.campos_valor((campos_linha(linha)))), chave_esquema(e)) ==
    Some{linha} : Maybe<&2, D.Linha>}

def campos_linha(linha: D.Linha) -> List<&2, D.Campo>:
  D.Linha{k, fs} = linha
  fs

def chave_esquema(e: D.EsquemaTabela) -> String:
  D.EsquemaTabela{n, k, cs} = e
  k

def linha_reconstroi(e, linha, valida):
  match e linha:
    case D.EsquemaTabela{n, +k, cs} D.Linha{id, fs}:
      correta = F.e_booleano_direita(D.unicode_valido(id) && D.campos_validos(cs, fs),
        D.chave_correta(D.achar_campo(fs, k), id), valida)
      %Equal.sym(Maybe<&2, List<&2, D.Campo>>, E.campos(D.campos_valor(fs)), Some{fs},
        campos_reconstroem(fs)) :
        {E.linha_campos(_, k) == Some{D.Linha{id, fs}} : Maybe<&2, D.Linha>}
      chave_reconstroi(D.achar_campo(fs, k), id, fs, correta)

law linhas_reconstroem:
  for +xs: List<&2, D.Linha>
  for +e: D.EsquemaTabela
  for +valida: {D.linhas_validas(xs, e) == True{} : Bool}
  {E.linhas(D.linhas_valor(xs), chave_esquema(e)) == Some{xs} : Maybe<&2, List<&2, D.Linha>>}
def linhas_reconstroem(xs, e, valida):
  match xs e:
    case Nil{} D.EsquemaTabela{n, k, cs}:
      {==}
    case Con{D.Linha{id, fs}, t} D.EsquemaTabela{n, k, cs}:
      +e0 = {D.EsquemaTabela{n, k, cs} : D.EsquemaTabela}
      primeira = F.e_booleano_esquerda(D.linha_valida(e0, D.Linha{id, fs}) && D.linhas_depois(t, id),
        D.linhas_validas(t, e0), valida)
      cabeca = F.e_booleano_esquerda(D.linha_valida(e0, D.Linha{id, fs}), D.linhas_depois(t, id), primeira)
      cauda = F.e_booleano_direita(D.linha_valida(e0, D.Linha{id, fs}) && D.linhas_depois(t, id), D.linhas_validas(t, e0), valida)
      %Equal.sym(Maybe<&2, D.Linha>, E.linha_campos(E.campos(D.campos_valor(fs)), k), Some{D.Linha{id, fs}},
        linha_reconstroi(e0, D.Linha{id, fs}, cabeca)) :
        {E.juntar_linhas(_, E.linhas(D.linhas_valor(t), k)) == Some{Con{D.Linha{id, fs}, t}} : Maybe<&2, List<&2, D.Linha>>}
      %Equal.sym(Maybe<&2, List<&2, D.Linha>>, E.linhas(D.linhas_valor(t), k), Some{t}, linhas_reconstroem(t, e0, cauda)) :
        {E.juntar_linhas(Some{D.Linha{id, fs}}, _) == Some{Con{D.Linha{id, fs}, t}} : Maybe<&2, List<&2, D.Linha>>}
      {==}

law tabela_reconstroi:
  for +e: D.EsquemaTabela
  for +t: D.Tabela
  for nome: {String.eq(D.esquema_nome(e), nome_tabela(t)) == True{} : Bool}
  for linhas: {D.linhas_validas(linhas_tabela(t), e) == True{} : Bool}
  {E.tabela(tabela_valor(t), e) == Some{t} : Maybe<&2, D.Tabela>}

def nome_tabela(t: D.Tabela) -> String:
  D.Tabela{n, ls} = t
  n

def linhas_tabela(t: D.Tabela) -> List<&2, D.Linha>:
  D.Tabela{n, ls} = t
  ls

def tabela_valor(t: D.Tabela) -> D.Valor:
  D.Tabela{n, ls} = t
  D.VRegistro{"linhas", D.linhas_valor(ls), D.VRegistro{"nome", D.VTexto{n}, D.VRegistroVazio{}}}

def tabela_reconstroi(e, t, nome, linhas):
  match e t:
    case D.EsquemaTabela{esperado, k, cs} D.Tabela{n, ls}:
      %Equal.sym(Bool, String.eq(n, esperado), True{}, O.string_eq_inverso(esperado, n, nome)) :
        {E.tabela_linhas(_, n, E.linhas(D.linhas_valor(ls), k)) == Some{D.Tabela{n, ls}} : Maybe<&2, D.Tabela>}
      %Equal.sym(Maybe<&2, List<&2, D.Linha>>, E.linhas(D.linhas_valor(ls), k), Some{ls},
        linhas_reconstroem(ls, D.EsquemaTabela{esperado, k, cs}, linhas)) :
        {E.tabela_linhas(True{}, n, _) == Some{D.Tabela{n, ls}} : Maybe<&2, D.Tabela>}
      {==}

law tabelas_reconstroem:
  for +es: List<&2, D.EsquemaTabela>
  for +ts: List<&2, D.Tabela>
  for +valida: {D.tabelas_validas(es, ts) == True{} : Bool}
  {E.tabelas(D.tabelas_valor(ts), es) == Some{ts} : Maybe<&2, List<&2, D.Tabela>>}
def tabelas_reconstroem(es, ts, valida):
  match es ts:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{t, tr}:
      F.absurdo_booleano({E.tabelas(D.tabelas_valor(Con{t, tr}), Nil{}) == Some{Con{t, tr}} : Maybe<&2, List<&2, D.Tabela>>}, valida)
    case Con{e, er} Nil{}:
      F.absurdo_booleano({E.tabelas(D.tabelas_valor(Nil{}), Con{e, er}) == Some{Nil{}} : Maybe<&2, List<&2, D.Tabela>>}, valida)
    case Con{e, er} Con{D.Tabela{n, ls}, tr}:
      +primeira = F.e_booleano_esquerda(String.eq(D.esquema_nome(e), n) && D.linhas_validas(ls, e), D.tabelas_validas(er, tr), valida)
      nome = F.e_booleano_esquerda(String.eq(D.esquema_nome(e), n), D.linhas_validas(ls, e), primeira)
      linhas = F.e_booleano_direita(String.eq(D.esquema_nome(e), n), D.linhas_validas(ls, e), primeira)
      cauda = F.e_booleano_direita(String.eq(D.esquema_nome(e), n) && D.linhas_validas(ls, e), D.tabelas_validas(er, tr), valida)
      %Equal.sym(Maybe<&2, D.Tabela>, E.tabela(tabela_valor(D.Tabela{n, ls}), e), Some{D.Tabela{n, ls}},
        tabela_reconstroi(e, D.Tabela{n, ls}, nome, linhas)) :
        {E.juntar_tabelas(_, E.tabelas(D.tabelas_valor(tr), er)) == Some{Con{D.Tabela{n, ls}, tr}} : Maybe<&2, List<&2, D.Tabela>>}
      %Equal.sym(Maybe<&2, List<&2, D.Tabela>>, E.tabelas(D.tabelas_valor(tr), er), Some{tr}, tabelas_reconstroem(er, tr, cauda)) :
        {E.juntar_tabelas(Some{D.Tabela{n, ls}}, _) == Some{Con{D.Tabela{n, ls}, tr}} : Maybe<&2, List<&2, D.Tabela>>}
      {==}

law forma_reconstroi_estado:
  for +e: D.Esquema
  for +s: D.Estado
  for +estrutura: {D.estrutura(e, s) == True{} : Bool}
  {E.forma(D.estado_valor(s), e) == Some{s} : Maybe<&2, D.Estado>}
def forma_reconstroi_estado(e, s, estrutura):
  match e s:
    case D.Esquema{es} D.Estado{ts, us}:
      +primeira = F.e_booleano_esquerda(D.tabelas_validas(es, ts) && D.linhas_validas(us, D.esquema_usuarios()), D.credenciais_validas(us), estrutura)
      tabelas = F.e_booleano_esquerda(D.tabelas_validas(es, ts), D.linhas_validas(us, D.esquema_usuarios()), primeira)
      usuarios = F.e_booleano_direita(D.tabelas_validas(es, ts), D.linhas_validas(us, D.esquema_usuarios()), primeira)
      %Equal.sym(Maybe<&2, List<&2, D.Tabela>>, E.tabelas(D.tabelas_valor(ts), es), Some{ts}, tabelas_reconstroem(es, ts, tabelas)) :
        {E.juntar_estado(True{}, _, E.linhas(D.linhas_valor(us), "id")) == Some{D.Estado{ts, us}} : Maybe<&2, D.Estado>}
      %Equal.sym(Maybe<&2, List<&2, D.Linha>>, E.linhas(D.linhas_valor(us), "id"), Some{us}, linhas_reconstroem(us, D.esquema_usuarios(), usuarios)) :
        {E.juntar_estado(True{}, Some{ts}, _) == Some{D.Estado{ts, us}} : Maybe<&2, D.Estado>}
      {==}

law transporte_privado_preserva_estado:
  for +e: D.Esquema
  for +s: D.Estado
  for +estrutura: {D.estrutura(e, s) == True{} : Bool}
  {E.decodificar(D.estado_valor(s), e) == Some{s} : Maybe<&2, D.Estado>}
def transporte_privado_preserva_estado(e, s, estrutura):
  %Equal.sym(Maybe<&2, D.Estado>, E.forma(D.estado_valor(s), e), Some{s}, forma_reconstroi_estado(e, s, estrutura)) :
    {E.verificar_resultado(_, e) == Some{s} : Maybe<&2, D.Estado>}
  %Equal.sym(Bool, D.estrutura(e, s), True{}, estrutura) : {E.verificar(_, s) == Some{s} : Maybe<&2, D.Estado>}
  {==}

law requisicao_valida_preserva_todos_os_campos:
  for +r: P.Requisicao
  for valida: {D.valor_valido(P.requisicao_valor(r)) == True{} : Bool}
  {Q.extrair(P.requisicao_valor(r)) == Some{r} : Maybe<&2, P.Requisicao>}
def requisicao_valida_preserva_todos_os_campos(r, valida):
  %Equal.sym(Bool, D.valor_valido(P.requisicao_valor(r)), True{}, valida) :
    {Q.validar(_, Q.forma(P.requisicao_valor(r))) == Some{r} : Maybe<&2, P.Requisicao>}
  Q.forma_reconstroi_requisicao(r)

def verificar_sucesso(b: Bool, +s0: D.Estado, +s: D.Estado,
  obtido: {E.verificar(b, s0) == Some{s} : Maybe<&2, D.Estado>}) ->
  L.E<{b == True{} : Bool}, {s0 == s : D.Estado}>:
  match b:
    case False{}:
      L.ex_falso(L.E<{False{} == True{} : Bool}, {s0 == s : D.Estado}>, F.nenhum_nao_algum(D.Estado, s, obtido))
    case True{}:
      L.Ambos{{==}, F.algum_injetivo(D.Estado, s0, s, obtido)}

def verificar_resultado_fiel(q: Maybe<&2, D.Estado>, +e: D.Esquema, +s: D.Estado,
  obtido: {E.verificar_resultado(q, e) == Some{s} : Maybe<&2, D.Estado>}) ->
  {D.estrutura(e, s) == True{} : Bool}:
  match q:
    case None{}:
      L.ex_falso({D.estrutura(e, s) == True{} : Bool}, F.nenhum_nao_algum(D.Estado, s, obtido))
    case Some{+s0}:
      F.com_par({D.estrutura(e, s) == True{} : Bool}, {D.estrutura(e, s0) == True{} : Bool},
        {s0 == s : D.Estado}, verificar_sucesso(D.estrutura(e, s0), s0, s, obtido),
        estrutura => igualdade =>
          %igualdade : {D.estrutura(e, _) == True{} : Bool}
          estrutura)

law transporte_privado_so_devolve_estado_estruturado:
  for +v: D.Valor
  for +e: D.Esquema
  for +s: D.Estado
  for obtido: {E.decodificar(v, e) == Some{s} : Maybe<&2, D.Estado>}
  {D.estrutura(e, s) == True{} : Bool}
def transporte_privado_so_devolve_estado_estruturado(v, e, s, obtido):
  verificar_resultado_fiel(E.forma(v, e), e, s, obtido)

def escolher_sucesso(b: Bool, +r0: P.Requisicao, +r: P.Requisicao,
  obtido: {Q.escolher(b, r0) == Some{r} : Maybe<&2, P.Requisicao>}) ->
  L.E<{b == True{} : Bool}, {r == r0 : P.Requisicao}>:
  match b:
    case False{}:
      L.ex_falso(L.E<{False{} == True{} : Bool}, {r == r0 : P.Requisicao}>, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case True{}:
      L.Ambos{{==}, Equal.sym(P.Requisicao, r0, r, F.algum_injetivo(P.Requisicao, r0, r, obtido))}

def nomes_reconstroem(+n0: String, +n1: String, +n2: String, +n3: String,
  -args: D.Valor, -cod: String, -cred: String, -pi: String,
  +corretos: {String.eq(n0, "argumentos") && String.eq(n1, "codigo") &&
    String.eq(n2, "credencial") && String.eq(n3, "prova") == True{} : Bool}) ->
  {D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred},
    D.VRegistro{n3, D.VTexto{pi}, D.VRegistroVazio{}}}}} == P.requisicao_valor(P.Requisicao{cred, cod, args, pi}) : D.Valor}:
  +tres = F.e_booleano_esquerda(String.eq(n0, "argumentos") && String.eq(n1, "codigo") && String.eq(n2, "credencial"), String.eq(n3, "prova"), corretos)
  +dois = F.e_booleano_esquerda(String.eq(n0, "argumentos") && String.eq(n1, "codigo"), String.eq(n2, "credencial"), tres)
  e0 = O.string_igual(n0, "argumentos", F.e_booleano_esquerda(String.eq(n0, "argumentos"), String.eq(n1, "codigo"), dois))
  e1 = O.string_igual(n1, "codigo", F.e_booleano_direita(String.eq(n0, "argumentos"), String.eq(n1, "codigo"), dois))
  e2 = O.string_igual(n2, "credencial", F.e_booleano_direita(String.eq(n0, "argumentos") && String.eq(n1, "codigo"), String.eq(n2, "credencial"), tres))
  e3 = O.string_igual(n3, "prova", F.e_booleano_direita(String.eq(n0, "argumentos") && String.eq(n1, "codigo") && String.eq(n2, "credencial"), String.eq(n3, "prova"), corretos))
  %Equal.sym(String, n0, "argumentos", e0) : {D.VRegistro{_, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VRegistroVazio{}}}}} == P.requisicao_valor(P.Requisicao{cred, cod, args, pi}) : D.Valor}
  %Equal.sym(String, n1, "codigo", e1) : {D.VRegistro{"argumentos", args, D.VRegistro{_, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VRegistroVazio{}}}}} == P.requisicao_valor(P.Requisicao{cred, cod, args, pi}) : D.Valor}
  %Equal.sym(String, n2, "credencial", e2) : {D.VRegistro{"argumentos", args, D.VRegistro{"codigo", D.VTexto{cod}, D.VRegistro{_, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VRegistroVazio{}}}}} == P.requisicao_valor(P.Requisicao{cred, cod, args, pi}) : D.Valor}
  %Equal.sym(String, n3, "prova", e3) : {D.VRegistro{"argumentos", args, D.VRegistro{"codigo", D.VTexto{cod}, D.VRegistro{"credencial", D.VTexto{cred}, D.VRegistro{_, D.VTexto{pi}, D.VRegistroVazio{}}}}} == P.requisicao_valor(P.Requisicao{cred, cod, args, pi}) : D.Valor}
  {==}

law envelope_aceito_reconstroi_exatamente:
  for +v: D.Valor
  for +r: P.Requisicao
  for obtido: {Q.forma(v) == Some{r} : Maybe<&2, P.Requisicao>}
  {v == P.requisicao_valor(r) : D.Valor}
def envelope_aceito_reconstroi_exatamente(v, r, obtido):
  match v:
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VRegistroVazio{}}}}}:
      F.com_par(
        {D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VRegistroVazio{}}}}} == P.requisicao_valor(r) : D.Valor},
        {String.eq(n0, "argumentos") && String.eq(n1, "codigo") && String.eq(n2, "credencial") && String.eq(n3, "prova") == True{} : Bool},
        {r == P.Requisicao{cred, cod, args, pi} : P.Requisicao},
        escolher_sucesso(String.eq(n0, "argumentos") && String.eq(n1, "codigo") && String.eq(n2, "credencial") && String.eq(n3, "prova"), P.Requisicao{cred, cod, args, pi}, r, obtido),
        nomes => igualdade =>
          %Equal.sym(P.Requisicao, r, P.Requisicao{cred, cod, args, pi}, igualdade) :
            {D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VRegistroVazio{}}}}} == P.requisicao_valor(_) : D.Valor}
          nomes_reconstroem(n0, n1, n2, n3, args, cod, cred, pi, nomes))
    case D.VAusente{}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VBool{zb}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VInt{za, zb}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VTexto{zs}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VListaVazia{}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VLista{zh, zt}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistroVazio{}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VAusente{}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VBool{zb}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VInt{za, zb}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VTexto{zs}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VListaVazia{}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VLista{zh, zt}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistroVazio{}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VAusente{}, rest2}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VBool{zb}, rest2}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VInt{za, zb}, rest2}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VListaVazia{}, rest2}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VLista{zh, zt}, rest2}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VRegistroVazio{}, rest2}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VRegistro{zn, zv, zr}, rest2}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VAusente{}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VBool{zb}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VInt{za, zb}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VTexto{zs}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VListaVazia{}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VLista{zh, zt}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistroVazio{}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VAusente{}, rest3}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VBool{zb}, rest3}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VInt{za, zb}, rest3}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VListaVazia{}, rest3}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VLista{zh, zt}, rest3}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VRegistroVazio{}, rest3}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VRegistro{zn, zv, zr}, rest3}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VAusente{}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VBool{zb}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VInt{za, zb}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VTexto{zs}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VListaVazia{}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VLista{zh, zt}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistroVazio{}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VAusente{}, bottom}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VBool{zb}, bottom}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VInt{za, zb}, bottom}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VListaVazia{}, bottom}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VLista{zh, zt}, bottom}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VRegistroVazio{}, bottom}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VRegistro{zn, zv, zr}, bottom}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VAusente{}}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VBool{zb}}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VInt{za, zb}}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VTexto{zs}}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VListaVazia{}}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VLista{zh, zt}}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case D.VRegistro{n0, args, D.VRegistro{n1, D.VTexto{cod}, D.VRegistro{n2, D.VTexto{cred}, D.VRegistro{n3, D.VTexto{pi}, D.VRegistro{zn, zv, zr}}}}}:
      L.ex_falso({v == P.requisicao_valor(r) : D.Valor}, F.nenhum_nao_algum(P.Requisicao, r, obtido))

def validar_sucesso(b: Bool, -q: Maybe<&2, P.Requisicao>, +r: P.Requisicao,
  obtido: {Q.validar(b, q) == Some{r} : Maybe<&2, P.Requisicao>}) ->
  L.E<{b == True{} : Bool}, {q == Some{r} : Maybe<&2, P.Requisicao>}>:
  match b:
    case False{}:
      L.ex_falso(L.E<{False{} == True{} : Bool}, {q == Some{r} : Maybe<&2, P.Requisicao>}>, F.nenhum_nao_algum(P.Requisicao, r, obtido))
    case True{}:
      L.Ambos{{==}, obtido}

law extrair_preserva_valor_e_valida:
  for +v: D.Valor
  for +r: P.Requisicao
  for obtido: {Q.extrair(v) == Some{r} : Maybe<&2, P.Requisicao>}
  L.E<{D.valor_valido(v) == True{} : Bool}, {v == P.requisicao_valor(r) : D.Valor}>
def extrair_preserva_valor_e_valida(v, r, obtido):
  F.com_par(L.E<{D.valor_valido(v) == True{} : Bool}, {v == P.requisicao_valor(r) : D.Valor}>,
    {D.valor_valido(v) == True{} : Bool}, {Q.forma(v) == Some{r} : Maybe<&2, P.Requisicao>},
    validar_sucesso(D.valor_valido(v), Q.forma(v), r, obtido),
    valido => forma => L.Ambos{valido, envelope_aceito_reconstroi_exatamente(v, r, forma)})
