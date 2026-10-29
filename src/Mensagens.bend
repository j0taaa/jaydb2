# Resultados privados dos modulos nativos para o controlador.
# 0 + resposta publica; 1 + resultado privado; 2 = transporte interno invalido.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ./Entrada.bend as E
import ./Gerar.bend as G
import ./Transporte.bend as T

def prefixar(tag: U32, bytes: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match bytes:
    case None{}:
      [2]
    case Some{bs}:
      Con{tag, bs}

def erro(status: S.Status) -> List<&2, U32>:
  prefixar(0, P.enquadrar(S.resposta_valor(S.resposta_erro(status))))

def enquadramento(resultado: E.PreAutenticacao) -> List<&2, U32>:
  match resultado:
    case E.Pronta{s, r}:
      [1]
    case E.ErroMensagem{status}:
      erro(status)
    case E.ErroTransporte{}:
      [2]

def juntar(campo: List<&2, U32>, resto: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match resto:
    case None{}:
      None{}
    case Some{r}:
      T.juntar(campo, r)

def metadados(codigo: String, prova: String, instancia: String,
  vinculos: String) -> List<&2, U32>:
  prefixar(1, juntar(B.utf8(codigo), juntar(B.utf8(prova),
    T.juntar(B.utf8(instancia), B.utf8(vinculos)))))

def instancia_pronta(instancia: Maybe<&2, String>, codigo: String, prova: String,
  vinculos: String) -> List<&2, U32>:
  match instancia:
    case None{}:
      [2]
    case Some{fonte}:
      metadados(codigo, prova, fonte, vinculos)

def autenticacao(resultado: E.Analise) -> List<&2, U32>:
  match resultado:
    case E.Recebida{estado, P.Requisicao{credencial, +codigo, +argumentos, +prova}, +contexto}:
      instancia_pronta(G.instancia(contexto, argumentos), codigo, prova, G.vinculos(codigo))
    case E.Rejeitada{status}:
      erro(status)
    case E.TransporteInvalido{}:
      [2]
