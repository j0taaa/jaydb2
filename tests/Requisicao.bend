import Base
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../src/Requisicao.bend as R

law argumentos_ausentes_sao_valor_explicito:
  {R.extrair(P.requisicao_valor(P.Requisicao{"", "", D.VAusente{}, ""})) ==
    Some{P.Requisicao{"", "", D.VAusente{}, ""}} : Maybe<&2, P.Requisicao>}
def argumentos_ausentes_sao_valor_explicito():
  {==}

law rejeita_argumentos_omitidos:
  {R.extrair(D.VRegistro{"codigo", D.VTexto{"p"},
    D.VRegistro{"credencial", D.VTexto{"c"},
      D.VRegistro{"prova", D.VTexto{"pi"}, D.VRegistroVazio{}}}}) ==
        None{} : Maybe<&2, P.Requisicao>}
def rejeita_argumentos_omitidos():
  {==}

law rejeita_codigo_com_tipo_incorreto:
  {R.extrair(D.VRegistro{"argumentos", D.VAusente{},
    D.VRegistro{"codigo", D.VBool{False{}},
      D.VRegistro{"credencial", D.VTexto{"c"},
        D.VRegistro{"prova", D.VTexto{"pi"}, D.VRegistroVazio{}}}}}) ==
          None{} : Maybe<&2, P.Requisicao>}
def rejeita_codigo_com_tipo_incorreto():
  {==}

law rejeita_campo_adicional:
  {R.extrair(D.VRegistro{"argumentos", D.VAusente{},
    D.VRegistro{"codigo", D.VTexto{"p"},
      D.VRegistro{"credencial", D.VTexto{"c"},
        D.VRegistro{"outro", D.VAusente{},
          D.VRegistro{"prova", D.VTexto{"pi"}, D.VRegistroVazio{}}}}}}) ==
            None{} : Maybe<&2, P.Requisicao>}
def rejeita_campo_adicional():
  {==}

law preserva_codigo_e_prova_unicode:
  {R.extrair(P.requisicao_valor(P.Requisicao{"c", "# ç 𝄞\n", D.VAusente{}, "# π\n"})) ==
    Some{P.Requisicao{"c", "# ç 𝄞\n", D.VAusente{}, "# π\n"}} : Maybe<&2, P.Requisicao>}
def preserva_codigo_e_prova_unicode():
  {==}
