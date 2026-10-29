# Fronteiras logicas da configuracao revisada, sem um Ambiente artificial.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Semantica.bend as S
import ../../contrato/Protocolo.bend as P
import ../../contrato/Bytes.bend as B
import ../../contrato/Requisitos.bend as R
import ../../contrato/Recursos.bend as X

law tres_tamanhos_zero_em_mensagem_e_estado_sao_permitidos:
  {R.limites_validos(S.Limites{0n, 0n, 256n}) == True{} : Bool}
def tres_tamanhos_zero_em_mensagem_e_estado_sao_permitidos():
  {==}

law resposta_precisa_comportar_os_erros:
  {R.limites_validos(S.Limites{1024n, 1024n, 0n}) == False{} : Bool}
def resposta_precisa_comportar_os_erros():
  {==}

law mensagem_exatamente_no_teto_e_admitida:
  {X.decidir_recepcao_em(S.Limites{1n, 0n, 256n}, X.CorpoRecebido{0, 1, [0]}) ==
    X.ProcessarCorpo{[0]} : X.Disposicao}
def mensagem_exatamente_no_teto_e_admitida():
  {==}

law mensagem_acima_do_teto_fecha_com_limite:
  {X.decidir_recepcao_em(S.Limites{1n, 0n, 256n}, X.CorpoRecebido{0, 2, [0, 0]}) ==
    X.RecusarEncerrar{S.Limite{}} : X.Disposicao}
def mensagem_acima_do_teto_fecha_com_limite():
  {==}

def bytes_resultado(r: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case None{}:
      Nil{}
    case Some{bs}:
      bs

def estado() -> D.Estado:
  D.Estado{Nil{}, Nil{}}

def tamanho_estado() -> Nat:
  B.comprimento(bytes_resultado(P.codificar(D.estado_valor(estado()))))

def configuracao(teto: Nat) -> S.Configuracao:
  S.Configuracao{D.Esquema{Nil{}}, S.NenhumaLei{}, S.Limites{0n, teto, 256n}, "testes-tres-limites"}

law estado_exatamente_no_teto_conserva_validade_estrutural:
  {R.estrutura(configuracao(tamanho_estado()), estado()) == True{} : Bool}
def estado_exatamente_no_teto_conserva_validade_estrutural():
  {==}

law estado_um_byte_acima_do_teto_continua_invalido:
  {R.estrutura(configuracao(Nat.sub(tamanho_estado(), 1n)), estado()) == False{} : Bool}
def estado_um_byte_acima_do_teto_continua_invalido():
  {==}
