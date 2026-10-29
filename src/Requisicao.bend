# Forma exata do envelope publico. A validacao nao interpreta codigo ou prova.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P

def escolher(ok: Bool, requisicao: P.Requisicao) -> Maybe<&2, P.Requisicao>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Some{requisicao}

def forma(v: D.Valor) -> Maybe<&2, P.Requisicao>:
  match v:
    case D.VRegistro{n0, argumentos,
      D.VRegistro{n1, D.VTexto{codigo},
        D.VRegistro{n2, D.VTexto{credencial},
          D.VRegistro{n3, D.VTexto{prova}, D.VRegistroVazio{}}}}}:
      escolher(String.eq(n0, "argumentos") && String.eq(n1, "codigo") &&
        String.eq(n2, "credencial") && String.eq(n3, "prova"),
        P.Requisicao{credencial, codigo, argumentos, prova})
    case _:
      None{}

def validar(ok: Bool, resultado: Maybe<&2, P.Requisicao>) -> Maybe<&2, P.Requisicao>:
  match ok:
    case False{}:
      None{}
    case True{}:
      resultado

def extrair(+v: D.Valor) -> Maybe<&2, P.Requisicao>:
  validar(D.valor_valido(v), forma(v))

law forma_reconstroi_requisicao:
  for r: P.Requisicao
  {forma(P.requisicao_valor(r)) == Some{r} : Maybe<&2, P.Requisicao>}

def forma_reconstroi_requisicao(r):
  match r:
    case P.Requisicao{credencial, codigo, argumentos, prova}:
      {==}
