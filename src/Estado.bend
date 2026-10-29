# Transporte privado do estado. O cliente so envia argumentos e nunca recebe
# acesso a este valor; o estado publicado e mantido pelo controlador do nucleo.
import Base
import ../contrato/Dados.bend as D

def campos_cons(nome: String, valor: D.Valor,
  resto: Maybe<&2, List<&2, D.Campo>>) -> Maybe<&2, List<&2, D.Campo>>:
  match resto:
    case None{}:
      None{}
    case Some{cs}:
      Some{Con{D.Campo{nome, valor}, cs}}

def campos(v: D.Valor) -> Maybe<&2, List<&2, D.Campo>>:
  match v:
    case D.VRegistroVazio{}:
      Some{Nil{}}
    case D.VRegistro{nome, valor, resto}:
      campos_cons(nome, valor, campos(resto))
    case _:
      None{}

def linha_chave(v: Maybe<&2, D.Valor>, cs: List<&2, D.Campo>) -> Maybe<&2, D.Linha>:
  match v:
    case Some{D.VTexto{k}}:
      Some{D.Linha{k, cs}}
    case _:
      None{}

def linha_campos(cs: Maybe<&2, List<&2, D.Campo>>, chave: String) -> Maybe<&2, D.Linha>:
  match cs:
    case None{}:
      None{}
    case Some{+fs}:
      linha_chave(D.achar_campo(fs, chave), fs)

def juntar_linhas(h: Maybe<&2, D.Linha>, t: Maybe<&2, List<&2, D.Linha>>) -> Maybe<&2, List<&2, D.Linha>>:
  match h t:
    case Some{linha} Some{resto}:
      Some{Con{linha, resto}}
    case _ _:
      None{}

def linhas(v: D.Valor, +chave: String) -> Maybe<&2, List<&2, D.Linha>>:
  match v:
    case D.VListaVazia{}:
      Some{Nil{}}
    case D.VLista{h, t}:
      juntar_linhas(linha_campos(campos(h), chave), linhas(t, chave))
    case _:
      None{}

def tabela_linhas(ok: Bool, nome: String, ls: Maybe<&2, List<&2, D.Linha>>) -> Maybe<&2, D.Tabela>:
  match ok ls:
    case True{} Some{rs}:
      Some{D.Tabela{nome, rs}}
    case _ _:
      None{}

def tabela(v: D.Valor, esquema: D.EsquemaTabela) -> Maybe<&2, D.Tabela>:
  match v esquema:
    case D.VRegistro{n0, ls, D.VRegistro{n1, D.VTexto{+nome}, D.VRegistroVazio{}}}
      D.EsquemaTabela{esperado, chave, cs}:
      tabela_linhas(String.eq(n0, "linhas") && String.eq(n1, "nome") &&
        String.eq(nome, esperado), nome, linhas(ls, chave))
    case _ _:
      None{}

def juntar_tabelas(h: Maybe<&2, D.Tabela>, t: Maybe<&2, List<&2, D.Tabela>>) -> Maybe<&2, List<&2, D.Tabela>>:
  match h t:
    case Some{tabela} Some{resto}:
      Some{Con{tabela, resto}}
    case _ _:
      None{}

def tabelas(v: D.Valor, esquemas: List<&2, D.EsquemaTabela>) -> Maybe<&2, List<&2, D.Tabela>>:
  match v esquemas:
    case D.VListaVazia{} Nil{}:
      Some{Nil{}}
    case D.VLista{h, t} Con{eh, et}:
      juntar_tabelas(tabela(h, eh), tabelas(t, et))
    case _ _:
      None{}

def juntar_estado(ok: Bool, ts: Maybe<&2, List<&2, D.Tabela>>,
  us: Maybe<&2, List<&2, D.Linha>>) -> Maybe<&2, D.Estado>:
  match ok ts us:
    case True{} Some{t} Some{u}:
      Some{D.Estado{t, u}}
    case _ _ _:
      None{}

def forma(v: D.Valor, esquema: D.Esquema) -> Maybe<&2, D.Estado>:
  match v esquema:
    case D.VRegistro{n0, ts, D.VRegistro{n1, us, D.VRegistroVazio{}}} D.Esquema{es}:
      juntar_estado(String.eq(n0, "tabelas") && String.eq(n1, "usuarios"),
        tabelas(ts, es), linhas(us, "id"))
    case _ _:
      None{}

def verificar(ok: Bool, estado: D.Estado) -> Maybe<&2, D.Estado>:
  match ok:
    case True{}:
      Some{estado}
    case False{}:
      None{}

def verificar_resultado(resultado: Maybe<&2, D.Estado>, esquema: D.Esquema) -> Maybe<&2, D.Estado>:
  match resultado:
    case None{}:
      None{}
    case Some{+s}:
      verificar(D.estrutura(esquema, s), s)

def decodificar(v: D.Valor, +esquema: D.Esquema) -> Maybe<&2, D.Estado>:
  verificar_resultado(forma(v, esquema), esquema)
