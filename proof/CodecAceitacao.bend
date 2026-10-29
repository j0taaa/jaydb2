# SOUNDNESS geral: bytes realmente aceitos sao exatamente P.codificar(v).
# A recursao e lexicografica em (comprimento, fase, filhos, campos).
# O indice Nat e o comprimento matematico: nenhuma quota nova do parser.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecAridades.bend as A
import ./CodecLimitesSequencias.bend as S
import ./CodecMontagem.bend as M
import ./CodecMontagemFechada.bend as MF
import ./CodecMontagemOrdem.bend as MO
import ./CodecRelaxar.bend as Relaxar
import ./CodecAceitacaoPalavra.bend as W
import ./CodecAceitacaoFilhos.bend as H
import ./CodecAceitacaoRegistro.bend as G
import ./CodecAceitacaoInducao.bend as I
import ./CodecAceitacaoPreparacao.bend as Q

def codificacao_de_registro_fechado(+xs: List<&2, S.CampoSegmentado>, +q: B.Numero64, -v: D.Valor,
  fechado: L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
    L.E<A.CamposOrdenados(S.campos(xs), ""), P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>>) ->
  P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs))):
  match fechado:
    case L.Ambos{medida, L.Ambos{ordem, codificado}}:
      codificado

def fechar_caso(+n: Nat, +bs: List<&2, U32>, -v: D.Valor,
  caso: Q.Caso<bs, v, n>,
  valores: @xs: List<&2, S.ValorSegmentado> -> H.FilhosLidos(xs, n) ->
    {B.octetos_validos(S.bytes_valores(xs)) == True{} : Bool} -> S.ValoresCanonicos(xs),
  campos: @ys: List<&2, S.CampoSegmentado> -> G.CamposLidos(ys, n) ->
    {B.octetos_validos(S.bytes_campos(ys)) == True{} : Bool} -> S.CamposCanonicos(ys)) -> P.Codificacao(v, bs):
  match caso:
    case Q.Canonico{codificado}:
      codificado
    case Q.Lista{+q, +xs, bytes, entrega, filhos, octetos}:
      F.com_par(P.Codificacao(v, bs),
        {B.nat64(S.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>},
        P.Codificacao(v, M.prefixo(5, q, S.bytes_valores(xs))),
        MF.lista_fechada_tem_medida_e_codificacao_canonica(xs, q, v, valores(xs, filhos, octetos), entrega),
        medida => codificado =>
          (%Equal.sym(List<&2, U32>, bs, M.prefixo(5, q, S.bytes_valores(xs)), bytes) : P.Codificacao(v, _)
            codificado))
    case Q.Registro{+q, +xs, bytes, entrega, filhos, octetos}:
      %Equal.sym(List<&2, U32>, bs, M.prefixo(6, q, S.bytes_campos(xs)), bytes) : P.Codificacao(v, _)
      codificacao_de_registro_fechado(xs, q, v,
        MO.registro_fechado_extrai_medida_ordem_e_codificacao_canonica(xs, q, v, campos(xs, filhos, octetos), entrega))

# fase 0 resolve UM valor; fase 1 resolve os filhos de uma lista;
# fase 2 resolve os valores dos campos, cujos nomes ja foram invertidos.
# A fase de filhos so chama a fase 0 com o mesmo n, que e menor que o
# comprimento admitido pelo valor pai. Cada cauda diminui estruturalmente.
law resolver:
  for +n: Nat
  for fase: Nat
  for +xs: List<&2, S.ValorSegmentado>
  for +ys: List<&2, S.CampoSegmentado>
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +v: D.Valor
  for prova: I.Obrigacao(n, fase, xs, ys, bs, corpo, teto, v)
  I.Conclusao(fase, xs, ys, bs, v)
def resolver(n, fase, xs, ys, bs, corpo, teto, v, prova):
  match n fase xs ys bs:
    case 0n 0n _ _ Nil{}:
      match prova:
        case L.Ambos{limite, L.Ambos{octetos, pronto}}:
          L.ex_falso(P.Codificacao(v, Nil{}), A.tag_nao_e_pronto(C.Raiz{}, v, pronto))
    case 0n 0n _ _ Con{b, t}:
      match prova:
        case L.Ambos{limite, resto}:
          F.absurdo_booleano(P.Codificacao(v, bs), limite)
    case 1n+p 0n _ _ _:
      match prova:
        case L.Ambos{limite, L.Ambos{octetos, pronto}}:
          +menor = p
          fechar_caso(menor, bs, v, Q.preparar_raiz(menor, bs, corpo, teto, v, limite, octetos, pronto),
            filhos => lidos => validos =>
              resolver(menor, 1n, filhos, Nil{}, Nil{}, B.Numero64{0, 0}, B.Numero64{0, 0}, D.VAusente{}, L.Ambos{lidos, validos}),
            campos => lidos => validos =>
              resolver(menor, 2n, Nil{}, campos, Nil{}, B.Numero64{0, 0}, B.Numero64{0, 0}, D.VAusente{}, L.Ambos{lidos, validos}))
    case _ 1n Nil{} _ _:
      Unit{}
    case _ 1n Con{S.ValorSegmentado{+h, +hb}, +resto} _ _:
      match prova:
        case L.Ambos{L.Ambos{H.FilhoLido{+hc, +ht, +fora, local, limite}, cauda}, validos}:
          F.com_par(S.ValoresCanonicos(xs),
            {B.octetos_validos(hb) == True{} : Bool}, {B.octetos_validos(S.bytes_valores(resto)) == True{} : Bool},
            W.separar_octetos_validos(hb, S.bytes_valores(resto), validos),
            cabeca_valida => cauda_valida => L.Ambos{
              resolver(n, 0n, Nil{}, Nil{}, hb, hc, ht, h,
                L.Ambos{limite, L.Ambos{cabeca_valida,
                  Relaxar.execucao_local_aceita_continua_aceita_sem_pilha_externa(hb, fora, hc, ht, C.Tag{C.Raiz{}}, h, local)}}),
              resolver(n, 1n, resto, ys, bs, corpo, teto, v, L.Ambos{cauda, cauda_valida})})
    case _ 2n _ Nil{} _:
      Unit{}
    case _ 2n _ Con{S.CampoSegmentado{+nome, +h, +nb, +hb}, +resto} _:
      match prova:
        case L.Ambos{L.Ambos{nome_valido, L.Ambos{nome_canonico, L.Ambos{H.FilhoLido{+hc, +ht, +fora, local, limite}, cauda}}}, validos}:
          F.com_par(S.CamposCanonicos(ys),
            {B.octetos_validos(B.concatenar(nb, hb)) == True{} : Bool}, {B.octetos_validos(S.bytes_campos(resto)) == True{} : Bool},
            W.separar_octetos_validos(B.concatenar(nb, hb), S.bytes_campos(resto), validos),
            par_valido => cauda_valida =>
              F.com_par(S.CamposCanonicos(ys), {B.octetos_validos(nb) == True{} : Bool}, {B.octetos_validos(hb) == True{} : Bool},
                W.separar_octetos_validos(nb, hb, par_valido),
                bytes_nome => bytes_valor => L.Ambos{nome_valido, L.Ambos{nome_canonico, L.Ambos{
                  resolver(n, 0n, Nil{}, Nil{}, hb, hc, ht, h,
                    L.Ambos{limite, L.Ambos{bytes_valor,
                      Relaxar.execucao_local_aceita_continua_aceita_sem_pilha_externa(hb, fora, hc, ht, C.Tag{C.Raiz{}}, h, local)}}),
                  resolver(n, 2n, xs, resto, bs, corpo, teto, v, L.Ambos{cauda, cauda_valida})}}}))
    case _ 3n+p _ _ _:
      Unit{}

law toda_execucao_raiz_pronta_reconstroi_a_codificacao_original:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +v: D.Valor
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for pronto: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
  P.Codificacao(v, bs)
def toda_execucao_raiz_pronta_reconstroi_a_codificacao_original(bs, corpo, teto, v, validos, pronto):
  resolver(B.comprimento(bs), 0n, Nil{}, Nil{}, bs, corpo, teto, v,
    L.Ambos{S.limite_reflexivo(B.comprimento(bs)), L.Ambos{validos, pronto}})

def aceitar_entrada_conferida(+bs: List<&2, U32>, +teto: B.Numero64, +v: D.Valor,
  entrada: R.EntradaConferida<B.nat64(B.comprimento(bs)), bs, teto, v>) -> P.Codificacao(v, bs):
  match entrada:
    case R.Conferida{+corpo, medida, cabe, octetos, percurso}:
      toda_execucao_raiz_pronta_reconstroi_a_codificacao_original(bs, corpo, teto, v, octetos,
        R.percurso_aceito_termina_pronto(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}, v, percurso))

# Unica premissa: a igualdade de ACEITACAO da API publica real.
# Nenhum Ambiente, canonicidade de filho, segmentacao ou contagem e recebido.
law toda_aceitacao_publica_tem_codificacao_canonica:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  P.Codificacao(v, bs)
def toda_aceitacao_publica_tem_codificacao_canonica(bs, teto, v, aceito):
  aceitar_entrada_conferida(bs, teto, v,
    R.aceitacao_exige_corpo_representavel_octetos_e_limite(bs, teto, v, aceito))
