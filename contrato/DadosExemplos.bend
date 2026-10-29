# Exemplos fechados de casos de borda da semantica de dados.
import Base
import ./Dados.bend as D

def esquema() -> D.Esquema:
  D.Esquema{[D.EsquemaTabela{"carros", "id", [D.Coluna{"id", D.Texto{}, False{}}, D.Coluna{"modelo", D.Texto{}, True{}}]}]}

def inicial() -> D.Estado:
  D.Estado{[D.Tabela{"carros", [D.Linha{"c1", [D.Campo{"id", D.VTexto{"c1"}}, D.Campo{"modelo", D.VAusente{}}]}]}], Nil{}}

law estado_bem_formado:
  {D.estrutura(esquema(), inicial()) == True{} : Bool}

def estado_bem_formado():
  {==}

law linha_ausente_distinta:
  {D.operar(esquema(), inicial(), D.LerCelula{D.Aplicacao{"carros"}, "c2", "modelo"}) == D.Observado{D.LinhaAusente{}} : D.ResultadoOp}

def linha_ausente_distinta():
  {==}

law coluna_ausente_distinta:
  {D.operar(esquema(), inicial(), D.LerCelula{D.Aplicacao{"carros"}, "c1", "modelo"}) == D.Observado{D.Celula{D.VAusente{}}} : D.ResultadoOp}

def coluna_ausente_distinta():
  {==}

law escrita_em_linha_ausente_nao_informa:
  {D.operar(esquema(), inicial(), D.DefinirColuna{D.Aplicacao{"carros"}, "c2", "modelo", D.VTexto{"X"}}) == D.Alterado{inicial()} : D.ResultadoOp}

def escrita_em_linha_ausente_nao_informa():
  {==}

law chave_divergente_e_erro_mesmo_sem_linha:
  {D.operar(esquema(), inicial(), D.DefinirColuna{D.Aplicacao{"carros"}, "c2", "id", D.VTexto{"outro"}}) == D.FalhaDados{} : D.ResultadoOp}

def chave_divergente_e_erro_mesmo_sem_linha():
  {==}

law tabela_inexistente_e_erro:
  {D.operar(esquema(), inicial(), D.RemoverLinha{D.Aplicacao{"outros"}, "c1"}) == D.FalhaDados{} : D.ResultadoOp}

def tabela_inexistente_e_erro():
  {==}

# U+D800 e um surrogate, portanto nao e um escalar Unicode valido.
law chave_unicode_invalida_e_erro:
  {D.operar(esquema(), inicial(), D.VerExistencia{D.Aplicacao{"carros"}, SCon{Chr{55296}, SNil{}}}) == D.FalhaDados{} : D.ResultadoOp}

def chave_unicode_invalida_e_erro():
  {==}
