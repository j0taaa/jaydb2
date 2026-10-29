# Instancia positiva com TRES leis proposicionais e uma leitura real.
# O certificado e universal em s; nenhuma lei e um teste booleano.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Semantica.bend as S
import ../../contrato/Requisitos.bend as R
import ../../contrato/Interface.bend as I
import ../../contrato/Logica.bend as L
import ../../src/Nucleo.bend as N
import ../../proof/Seguranca.bend as G
import ../../proof/Preparacao.bend as P
import ../../proof/Maquina.bend as M
import ../../proof/Publicacao.bend as U
import ../../proof/Fundamentos.bend as F
import ../../contrato/Protocolo.bend as Wire
import ../../src/Execucao.bend as X
import ../../src/Entrada.bend as E
import ../../proof/Adaptadores.bend as A

def contexto() -> D.Contexto:
  D.Contexto{"b", "pessoa"}

def argumentos() -> D.Valor:
  D.VTexto{"argumento exato"}

def codigo() -> String:
  "programa de teste: contar usuarios e terminar"

def operacao() -> D.Operacao:
  D.ContarLinhas{D.Usuarios{}}

def traco(s: D.Estado) -> List<&2, S.Evento>:
  D.Estado{ts, us} = s
  [S.Evento{operacao(), S.Leitura{D.Quantidade{List.length(&2, D.Linha, us)}}}]

def estado_inalterado(h: S.Situacao) -> Type:
  match h:
    case S.Estavel{s}:
      Unit
    case S.Executando{s, ctx, cod, args, w, ts}:
      {w == s : D.Estado}
    case S.Encerrada{s, ctx, cod, args, w, ts, r}:
      {w == s : D.Estado}

def so_a_leitura_declarada(h: S.Situacao) -> Type:
  match h:
    case S.Estavel{s}:
      Unit
    case S.Executando{s, ctx, cod, args, w, ts}:
      L.Ou<{ts == Nil{} : List<&2, S.Evento>}, {ts == traco(s) : List<&2, S.Evento>}>
    case S.Encerrada{s, ctx, cod, args, w, ts, r}:
      L.Ou<{ts == Nil{} : List<&2, S.Evento>}, {ts == traco(s) : List<&2, S.Evento>}>

def origem_fixa(h: S.Situacao) -> Type:
  match h:
    case S.Estavel{s}:
      Unit
    case S.Executando{s, ctx, cod, args, w, ts}:
      L.E<{ctx == contexto() : D.Contexto}, L.E<{cod == codigo() : String}, {args == argumentos() : D.Valor}>>
    case S.Encerrada{s, ctx, cod, args, w, ts, r}:
      L.E<{ctx == contexto() : D.Contexto}, L.E<{cod == codigo() : String}, {args == argumentos() : D.Valor}>>

def configuracao() -> S.Configuracao:
  S.Configuracao{D.Esquema{Nil{}},
    S.MaisUmaLei{estado_inalterado, S.MaisUmaLei{so_a_leitura_declarada,
      S.MaisUmaLei{origem_fixa, S.NenhumaLei{}}}},
    S.Limites{1024n, 1024n, 256n}, "Bend-2.0.39-testes"}

def programa() -> S.Programa:
  S.Programa{ctx => args => S.Acessar{operacao(), retorno => S.Terminar{D.VAusente{}}}}

def usuario(+id: String, cred: String) -> D.Linha:
  D.Linha{id, [D.Campo{"credencial", D.VTexto{cred}}, D.Campo{"id", D.VTexto{id}},
    D.Campo{"tipo", D.VTexto{"pessoa"}}]}

def inicial() -> D.Estado:
  D.Estado{Nil{}, [usuario("a", "primeira"), usuario("b", "segunda")]}

def leis_executando(-s: D.Estado, -ts: List<&2, S.Evento>,
  leitura: L.Ou<{ts == Nil{} : List<&2, S.Evento>}, {ts == traco(s) : List<&2, S.Evento>}>) ->
  S.Cumpre(configuracao(), S.Executando{s, contexto(), codigo(), argumentos(), s, ts}):
  L.Ambos{{==}, L.Ambos{leitura, L.Ambos{L.Ambos{{==}, L.Ambos{{==}, {==}}}, Unit{}}}}

def leis_encerrada(-s: D.Estado, -ts: List<&2, S.Evento>, -r: S.Resposta,
  leitura: L.Ou<{ts == Nil{} : List<&2, S.Evento>}, {ts == traco(s) : List<&2, S.Evento>}>) ->
  S.Cumpre(configuracao(), S.Encerrada{s, contexto(), codigo(), argumentos(), s, ts, r}):
  L.Ambos{{==}, L.Ambos{leitura, L.Ambos{L.Ambos{{==}, L.Ambos{{==}, {==}}}, Unit{}}}}

def prefixo_zero(-s: D.Estado) -> R.SegurancaPrefixo(configuracao(), s,
  contexto(), codigo(), argumentos(), s, Nil{}):
  L.Ambos{leis_executando(s, Nil{}, L.Esquerda{{==}}),
    L.Ambos{leis_encerrada(s, Nil{}, S.resposta_erro(S.Limite{}), L.Esquerda{{==}}),
      leis_encerrada(s, Nil{}, S.resposta_erro(S.Falha{}), L.Esquerda{{==}})}}

def prefixo_lido(-s: D.Estado) -> R.SegurancaPrefixo(configuracao(), s,
  contexto(), codigo(), argumentos(), s, traco(s)):
  L.Ambos{leis_executando(s, traco(s), L.Direita{{==}}),
    L.Ambos{leis_encerrada(s, traco(s), S.resposta_erro(S.Limite{}), L.Direita{{==}}),
      leis_encerrada(s, traco(s), S.resposta_erro(S.Falha{}), L.Direita{{==}})}}

def publicacao_inalterada(r: S.Resposta, -s: D.Estado,
  valido: R.Valido(configuracao(), s)) -> R.PublicacaoValida(r, configuracao(), s):
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      valido
    case S.Resposta{S.Recusa{}, v}:
      Unit{}
    case S.Resposta{S.Entrada{}, v}:
      Unit{}
    case S.Resposta{S.Autenticacao{}, v}:
      Unit{}
    case S.Resposta{S.Certificado{}, v}:
      Unit{}
    case S.Resposta{S.Dados{}, v}:
      Unit{}
    case S.Resposta{S.Limite{}, v}:
      Unit{}
    case S.Resposta{S.Falha{}, v}:
      Unit{}

law certificado:
  R.Certifica(configuracao(), codigo(), programa(), contexto(), argumentos())
def certificado(s, valido, identidade, n):
  match s n:
    case D.Estado{ts, us} 0n:
      prefixo_zero(D.Estado{ts, us})
    case D.Estado{ts, us} 1n+m:
      match m:
        case 0n:
          prefixo_lido(D.Estado{ts, us})
        case 1n+k:
          %Equal.sym(S.Percurso,
            S.continuar_percurso(k, S.Parou{D.Estado{ts, us}, S.Resposta{S.Sucesso{}, D.VAusente{}}},
              D.Esquema{Nil{}}, traco(D.Estado{ts, us})),
            S.Final{D.Estado{ts, us}, traco(D.Estado{ts, us}), S.Resposta{S.Sucesso{}, D.VAusente{}}},
            M.referencia_parada(k, D.Estado{ts, us}, traco(D.Estado{ts, us}), S.Resposta{S.Sucesso{}, D.VAusente{}}, D.Esquema{Nil{}})) :
              R.SegurancaPercurso(_, configuracao(), D.Estado{ts, us}, contexto(), codigo(), argumentos())
          L.Ambos{prefixo_lido(D.Estado{ts, us}),
            L.Ambos{leis_encerrada(D.Estado{ts, us}, traco(D.Estado{ts, us}),
              R.finalizar(S.Resposta{S.Sucesso{}, D.VAusente{}}, configuracao(), D.Estado{ts, us}), L.Direita{{==}}),
              publicacao_inalterada(R.finalizar(S.Resposta{S.Sucesso{}, D.VAusente{}}, configuracao(), D.Estado{ts, us}),
                D.Estado{ts, us}, valido)}}

law termina:
  I.ProgramaTermina(configuracao(), programa())
def termina(s, ctx, args):
  match s:
    case D.Estado{+ts, +us}:
      (2n, D.Estado{ts, us}, traco(D.Estado{ts, us}), S.Resposta{S.Sucesso{}, D.VAusente{}}, {==})

law inicial_valido:
  R.Valido(configuracao(), inicial())
def inicial_valido():
  L.Ambos{{==}, L.Ambos{Unit{}, L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}}}

law contexto_real:
  {D.autenticar(inicial(), "segunda") == Some{contexto()} : Maybe<&2, D.Contexto>}
def contexto_real():
  {==}

law seguranca_geral_do_teste:
  for n: Nat
  R.SegurancaPercurso(N.percorrer(n, N.iniciar(programa(), contexto(), argumentos(), inicial()), S.esquema(configuracao())),
    configuracao(), inicial(), contexto(), codigo(), argumentos())
def seguranca_geral_do_teste(n):
  G.certificado_cobre_execucao_autenticada(configuracao(), codigo(), programa(), contexto(), argumentos(),
    certificado(), inicial(), inicial_valido(), "segunda", contexto_real(), n)

law publicacao_real_valida:
  R.Valido(configuracao(), S.publica(S.Resposta{S.Sucesso{}, D.VAusente{}}, inicial(), inicial()))
def publicacao_real_valida():
  G.conclusao_certificada_preserva_validade(S.Resposta{S.Sucesso{}, D.VAusente{}}, configuracao(), codigo(),
    programa(), contexto(), argumentos(), certificado(), inicial(), inicial_valido(), "segunda", contexto_real(),
    2n, inicial(), traco(inicial()), S.Resposta{S.Sucesso{}, D.VAusente{}}, {==}, {==})

law interrupcao_depois_da_leitura:
  S.Cumpre(configuracao(), S.Encerrada{inicial(), contexto(), codigo(), argumentos(),
    inicial(), traco(inicial()), S.resposta_erro(S.Falha{})})
def interrupcao_depois_da_leitura():
  G.interrupcao_certificada_preserva_todas_as_leis(G.PorFalha{}, configuracao(), codigo(), programa(), contexto(), argumentos(),
    certificado(), inicial(), inicial_valido(), "segunda", contexto_real(), 1n, S.Prefixo{inicial(), traco(inicial())}, {==})

law tamanho_e_payload_reais:
  P.Preparavel(S.limites(configuracao()), R.finalizar(S.Resposta{S.Sucesso{}, D.VAusente{}}, configuracao(), inicial()))
def tamanho_e_payload_reais():
  P.finalizar_garante_payload_e_tamanho(S.Resposta{S.Sucesso{}, D.VAusente{}}, configuracao(), inicial(), {==})

def resposta() -> S.Resposta:
  S.Resposta{S.Sucesso{}, D.VAusente{}}

def maquina_final() -> N.Maquina:
  N.Parada{inicial(), traco(inicial()), resposta()}

def preparada() -> N.Preparada:
  N.Preparada{inicial(), traco(inicial()), resposta(),
    F.extrair_ou(List<&2, U32>, Wire.enquadrar(S.resposta_valor(resposta())), Nil{})}

law preparacao_real_obtida:
  {N.preparar(maquina_final(), configuracao()) == Some{preparada()} : Maybe<&2, N.Preparada>}
def preparacao_real_obtida():
  {==}

law preparacao_real_fiel:
  P.Fiel(inicial(), traco(inicial()), R.finalizar(resposta(), configuracao(), inicial()), preparada())
def preparacao_real_fiel():
  P.preparar_preserva_resposta_estado_eventos_e_bytes(maquina_final(), configuracao(), preparada(), preparacao_real_obtida())

law ciclo_real_de_preparacao_e_publicacao_valido:
  R.Valido(configuracao(), U.publicado(N.concluir(preparada(), inicial())))
def ciclo_real_de_preparacao_e_publicacao_valido():
  U.conclusao_de_preparacao_certificada_e_valida(configuracao(), codigo(), programa(), contexto(), argumentos(),
    certificado(), inicial(), inicial_valido(), "segunda", contexto_real(), 2n, inicial(), traco(inicial()),
    resposta(), {==}, preparada(), preparacao_real_fiel())

def requisicao() -> Wire.Requisicao:
  Wire.Requisicao{"segunda", codigo(), argumentos(), "certificado do teste"}

law adaptador_requisicao_real:
  {E.autenticar(Some{requisicao()}, inicial()) == E.Recebida{inicial(), requisicao(), contexto()} : E.Analise}
def adaptador_requisicao_real():
  {==}

law identidade_do_adaptador_nao_vem_dos_argumentos:
  L.E<{inicial() == inicial() : D.Estado}, L.E<{requisicao() == requisicao() : Wire.Requisicao},
    {D.autenticar(inicial(), I.credencial(requisicao())) == Some{contexto()} : Maybe<&2, D.Contexto>}>>
def identidade_do_adaptador_nao_vem_dos_argumentos():
  A.entrada_recebida_tem_identidade_autentica(requisicao(), inicial(), requisicao(), inicial(), contexto(), adaptador_requisicao_real())

def primeira_iteracao() -> X.Iteracao:
  X.avancar(X.iniciar(programa(), contexto(), argumentos(), inicial()), configuracao())

def proxima(i: X.Iteracao) -> X.Iteracao:
  match i:
    case X.Continuar{estado}:
      X.avancar(estado, configuracao())
    case X.Preparar{estado}:
      X.avancar(estado, configuracao())
    case X.Encerrar{bytes}:
      X.Encerrar{bytes}
    case X.Inconsistente{}:
      X.Inconsistente{}

law loop_primeiro_passo_contem_leitura:
  {primeira_iteracao() == X.Continuar{X.EstadoExecucao{inicial(), N.EmCurso{inicial(), S.Terminar{D.VAusente{}}, traco(inicial())}}} : X.Iteracao}
def loop_primeiro_passo_contem_leitura():
  {==}

law loop_segundo_passo_pede_preparacao:
  {proxima(primeira_iteracao()) == X.Preparar{X.EstadoExecucao{inicial(), maquina_final()}} : X.Iteracao}
def loop_segundo_passo_pede_preparacao():
  {==}

law loop_terceiro_passo_prepara_e_conclui:
  {proxima(proxima(primeira_iteracao())) == X.concluir(N.concluir(preparada(), inicial())) : X.Iteracao}
def loop_terceiro_passo_prepara_e_conclui():
  {==}
