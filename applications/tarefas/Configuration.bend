import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Environment.bend as E
import ./Policy.bend as Policy
import ./Proofs.bend as Proofs

# Uma tabela por pessoa permite enumerar somente suas proprias tarefas.
def tabela(nome: String) -> D.EsquemaTabela:
  D.EsquemaTabela{nome, "id", [D.Coluna{"concluida", D.Booleano{}, False{}},
    D.Coluna{"id", D.Texto{}, False{}}, D.Coluna{"proprietario", D.Texto{}, False{}},
    D.Coluna{"titulo", D.Texto{}, False{}}]}

def esquema() -> D.Esquema:
  D.Esquema{[tabela("alice"), tabela("bob")]}

def limites() -> S.Limites:
  S.Limites{32768n, 65536n, 32768n}

def ambiente() -> String:
  E.identidade()

def config() -> S.Configuracao:
  Policy.config(esquema(), limites(), ambiente())
