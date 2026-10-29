# Ponte entre os contadores reais de C.Pilha e os bytes canonicos pendentes.
# O plano descreve irmaos ainda nao lidos, em ordem de leitura. No frame Nome
# inclui tambem o valor do campo atual; o nome atual pode ainda estar em curso.
# Nenhuma premissa afirma que o minimo cabe: isso e uma conclusao.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecTamanhos.bend as T
import ./CodecLimitesNomes.bend as N
import ./CodecLimitesSequencias.bend as S
import ./CodecMinimosPilha.bend as M
import ./CodecSomas.bend as A
import ./CodecSomasMinimos.bend as G
import ./CodecReservas.bend as R

type Plano is Data:
  Fim{}
  IrmaosValores{valores: List<&2, S.ValorSegmentado>, pai: Plano}
  IrmaosCampos{campos: List<&2, S.CampoSegmentado>, pai: Plano}
  ValorAposNome{valor: D.Valor, bytes: List<&2, U32>, campos: List<&2, S.CampoSegmentado>, pai: Plano}

# As unicas premissas numericas sao medidas de CONTAGENS de segmentos reais.
# Os acumuladores e o bit ultimo nao interferem no limite inferior.
def PlanoCanonico(pilha: C.Pilha, plano: Plano) -> Type:
  match pilha plano:
    case C.Raiz{} Fim{}:
      Unit
    case C.Lista{u, q, xs, pai} IrmaosValores{valores, acima}:
      L.E<{B.nat64(S.quantidade_valores(valores)) == Some{q} : Maybe<&2, B.Numero64>},
        L.E<S.ValoresCanonicos(valores), PlanoCanonico(pai, acima)>>
    case C.Campo{u, q, n, xs, pai} IrmaosCampos{campos, acima}:
      L.E<{B.nat64(S.quantidade_campos(campos)) == Some{q} : Maybe<&2, B.Numero64>},
        L.E<S.CamposCanonicos(campos), PlanoCanonico(pai, acima)>>
    case C.Nome{u, q, n, xs, pai} ValorAposNome{v, bs, campos, acima}:
      L.E<{B.nat64(S.quantidade_campos(campos)) == Some{q} : Maybe<&2, B.Numero64>},
        L.E<P.Codificacao(v, bs), L.E<S.CamposCanonicos(campos), PlanoCanonico(pai, acima)>>>
    case _ _:
      Empty

def bytes_pendentes(plano: Plano) -> List<&2, U32>:
  match plano:
    case Fim{}:
      Nil{}
    case IrmaosValores{xs, pai}:
      B.concatenar(S.bytes_valores(xs), bytes_pendentes(pai))
    case IrmaosCampos{xs, pai}:
      B.concatenar(S.bytes_campos(xs), bytes_pendentes(pai))
    case ValorAposNome{v, bs, xs, pai}:
      B.concatenar(bs, B.concatenar(S.bytes_campos(xs), bytes_pendentes(pai)))

def minimo_natural(plano: Plano) -> Nat:
  match plano:
    case Fim{}:
      0n
    case IrmaosValores{xs, pai}:
      Nat.add(S.quantidade_valores(xs), minimo_natural(pai))
    case IrmaosCampos{xs, pai}:
      Nat.add(Nat.mul(11n, S.quantidade_campos(xs)), minimo_natural(pai))
    case ValorAposNome{v, bs, xs, pai}:
      1n+Nat.add(Nat.mul(11n, S.quantidade_campos(xs)), minimo_natural(pai))

def Certificado(pilha: C.Pilha, +plano: Plano) -> Type:
  L.E<{C.minimo_pilha(pilha) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>},
    {Nat.is_le(minimo_natural(plano), B.comprimento(bytes_pendentes(plano))) == True{} : Bool}>

# A recursao consome apenas a pilha pai e o plano pai. Os limites das
# sequencias sao provados sobre as caudas dos respectivos segmentos.
law minimo_pilha_canonica_e_exato_e_limitado_pelos_bytes_pendentes:
  for +pilha: C.Pilha
  for +plano: Plano
  for canonico: PlanoCanonico(pilha, plano)
  Certificado(pilha, plano)
def minimo_pilha_canonica_e_exato_e_limitado_pelos_bytes_pendentes(pilha, plano, canonico):
  match pilha plano:
    case C.Raiz{} Fim{}:
      L.Ambos{{==}, {==}}
    case C.Lista{u, +q, xs, +pai} IrmaosValores{+valores, +acima}:
      match canonico:
        case L.Ambos{medido, L.Ambos{segmentos, anterior}}:
          F.com_par(Certificado(pilha, plano),
            {C.minimo_pilha(pai) == B.nat64(minimo_natural(acima)) : Maybe<&2, B.Numero64>},
            {Nat.is_le(minimo_natural(acima), B.comprimento(bytes_pendentes(acima))) == True{} : Bool},
            minimo_pilha_canonica_e_exato_e_limitado_pelos_bytes_pendentes(pai, acima, anterior),
            exato => limite => L.Ambos{
                (%Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(minimo_natural(acima)), exato) :
                  {C.somar_pendencia(q, 1n, _) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>}
                  %A.nat_somar_zero_direita(S.quantidade_valores(valores)) :
                    {C.somar_pendencia(q, 1n, B.nat64(minimo_natural(acima))) == B.nat64(Nat.add(_, minimo_natural(acima))) : Maybe<&2, B.Numero64>}
                  M.somar_pendencia_nat64_exato(S.quantidade_valores(valores), q, 1n, minimo_natural(acima), medido)),
                S.concatenar_segmentos_preserva_soma_dos_limites(S.bytes_valores(valores), bytes_pendentes(acima), S.quantidade_valores(valores), minimo_natural(acima),
                  S.sequencia_de_valores_canonicos_exige_um_octeto_por_valor(valores, segmentos), limite)})
    case C.Campo{u, +q, n, xs, +pai} IrmaosCampos{+campos, +acima}:
      match canonico:
        case L.Ambos{medido, L.Ambos{segmentos, anterior}}:
          F.com_par(Certificado(pilha, plano),
            {C.minimo_pilha(pai) == B.nat64(minimo_natural(acima)) : Maybe<&2, B.Numero64>},
            {Nat.is_le(minimo_natural(acima), B.comprimento(bytes_pendentes(acima))) == True{} : Bool},
            minimo_pilha_canonica_e_exato_e_limitado_pelos_bytes_pendentes(pai, acima, anterior),
            exato => limite => L.Ambos{
                (%Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(minimo_natural(acima)), exato) :
                  {C.somar_pendencia(q, 11n, _) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>}
                  M.somar_pendencia_nat64_exato(S.quantidade_campos(campos), q, 11n, minimo_natural(acima), medido)),
                S.concatenar_segmentos_preserva_soma_dos_limites(S.bytes_campos(campos), bytes_pendentes(acima), Nat.mul(11n, S.quantidade_campos(campos)), minimo_natural(acima),
                  S.sequencia_de_campos_canonicos_exige_onze_octetos_por_campo(campos, segmentos), limite)})
    case C.Nome{u, +q, n, xs, +pai} ValorAposNome{+v, +bs, +campos, +acima}:
      match canonico:
        case L.Ambos{medido, L.Ambos{valor, L.Ambos{segmentos, anterior}}}:
          F.com_par(Certificado(pilha, plano),
            {C.minimo_pilha(pai) == B.nat64(minimo_natural(acima)) : Maybe<&2, B.Numero64>},
            {Nat.is_le(minimo_natural(acima), B.comprimento(bytes_pendentes(acima))) == True{} : Bool},
            minimo_pilha_canonica_e_exato_e_limitado_pelos_bytes_pendentes(pai, acima, anterior),
            exato => limite => L.Ambos{
                (%Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(minimo_natural(acima)), exato) :
                  {C.somar_opcionais(Some{B.Numero64{0, 1}}, C.somar_pendencia(q, 11n, _)) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>}
                  %Equal.sym(Maybe<&2, B.Numero64>, C.somar_pendencia(q, 11n, B.nat64(minimo_natural(acima))), B.nat64(Nat.add(Nat.mul(11n, S.quantidade_campos(campos)), minimo_natural(acima))),
                    M.somar_pendencia_nat64_exato(S.quantidade_campos(campos), q, 11n, minimo_natural(acima), medido)) :
                    {C.somar_opcionais(B.nat64(1n), _) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>}
                  A.somar_opcionais_nat64_exato(1n, Nat.add(Nat.mul(11n, S.quantidade_campos(campos)), minimo_natural(acima)))),
                S.concatenar_segmentos_preserva_soma_dos_limites(bs, B.concatenar(S.bytes_campos(campos), bytes_pendentes(acima)), 1n, Nat.add(Nat.mul(11n, S.quantidade_campos(campos)), minimo_natural(acima)),
                  T.todo_valor_canonico_exige_pelo_menos_um_octeto(v, bs, valor),
                  S.concatenar_segmentos_preserva_soma_dos_limites(S.bytes_campos(campos), bytes_pendentes(acima), Nat.mul(11n, S.quantidade_campos(campos)), minimo_natural(acima),
                    S.sequencia_de_campos_canonicos_exige_onze_octetos_por_campo(campos, segmentos), limite))})
    case C.Raiz{} IrmaosValores{valores, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Raiz{} IrmaosCampos{campos, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Raiz{} ValorAposNome{v, bs, campos, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Lista{u, q, xs, pai} Fim{}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Lista{u, q, xs, pai} IrmaosCampos{campos, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Lista{u, q, xs, pai} ValorAposNome{v, bs, campos, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Campo{u, q, n, xs, pai} Fim{}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Campo{u, q, n, xs, pai} IrmaosValores{valores, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Campo{u, q, n, xs, pai} ValorAposNome{v, bs, campos, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Nome{u, q, n, xs, pai} Fim{}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Nome{u, q, n, xs, pai} IrmaosValores{valores, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)
    case C.Nome{u, q, n, xs, pai} IrmaosCampos{campos, acima}:
      L.ex_falso(Certificado(pilha, plano), canonico)

# Os bytes ainda em curso podem preceder todas as pendencias da pilha.
# Esta lei permite usar o mesmo plano durante cabecalhos e conteudos.
law prefixo_atual_preserva_limite_da_pilha:
  for +pilha: C.Pilha
  for +plano: Plano
  for +atual: List<&2, U32>
  for canonico: PlanoCanonico(pilha, plano)
  L.E<{C.minimo_pilha(pilha) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>},
    {Nat.is_le(minimo_natural(plano), B.comprimento(B.concatenar(atual, bytes_pendentes(plano)))) == True{} : Bool}>
def prefixo_atual_preserva_limite_da_pilha(pilha, plano, atual, canonico):
  F.com_par(
    L.E<{C.minimo_pilha(pilha) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>},
      {Nat.is_le(minimo_natural(plano), B.comprimento(B.concatenar(atual, bytes_pendentes(plano)))) == True{} : Bool}>,
    {C.minimo_pilha(pilha) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>},
    {Nat.is_le(minimo_natural(plano), B.comprimento(bytes_pendentes(plano))) == True{} : Bool},
    minimo_pilha_canonica_e_exato_e_limitado_pelos_bytes_pendentes(pilha, plano, canonico),
    exato => limite => L.Ambos{exato,
        S.concatenar_segmentos_preserva_soma_dos_limites(atual, bytes_pendentes(plano), 0n, minimo_natural(plano),
          T.zero_natural_nao_maior(B.comprimento(atual)), limite)})

law minimo_pilha_canonica_cabe_no_sufixo_real:
  for +pilha: C.Pilha
  for +plano: Plano
  for +atual: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for canonico: PlanoCanonico(pilha, plano)
  for medido: {B.nat64(B.comprimento(B.concatenar(atual, bytes_pendentes(plano)))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.conferir(C.minimo_pilha(pilha), corpo, teto) == C.Cabe{} : C.Conferencia}
def minimo_pilha_canonica_cabe_no_sufixo_real(pilha, plano, atual, corpo, teto, canonico, medido, cabe):
  F.com_par({C.conferir(C.minimo_pilha(pilha), corpo, teto) == C.Cabe{} : C.Conferencia},
    {C.minimo_pilha(pilha) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>},
    {Nat.is_le(minimo_natural(plano), B.comprimento(B.concatenar(atual, bytes_pendentes(plano)))) == True{} : Bool},
    prefixo_atual_preserva_limite_da_pilha(pilha, plano, atual, canonico),
    exato => limite =>
      %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pilha), B.nat64(minimo_natural(plano)), exato) :
        {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
      R.minimo_natural_dentro_do_corpo_e_teto_u64_cabe(minimo_natural(plano), B.comprimento(B.concatenar(atual, bytes_pendentes(plano))), corpo, teto, medido, limite, cabe))

# Conteudo do campo cujo cabecalho acaba de ser lido. Para texto a contagem
# e literalmente a quantidade dos octetos; para containers conta segmentos.
type SegmentoAtual is Data:
  Octetos{bytes: List<&2, U32>}
  Valores{valores: List<&2, S.ValorSegmentado>}
  Campos{campos: List<&2, S.CampoSegmentado>}

def quantidade_atual(s: SegmentoAtual) -> Nat:
  match s:
    case Octetos{bs}:
      B.comprimento(bs)
    case Valores{xs}:
      S.quantidade_valores(xs)
    case Campos{xs}:
      S.quantidade_campos(xs)

def bytes_atuais(s: SegmentoAtual) -> List<&2, U32>:
  match s:
    case Octetos{bs}:
      bs
    case Valores{xs}:
      S.bytes_valores(xs)
    case Campos{xs}:
      S.bytes_campos(xs)

def SegmentoCompativel(f: C.Finalidade, s: SegmentoAtual) -> Type:
  match f s:
    case C.Inteiro{} Octetos{bs}:
      Unit
    case C.Texto{} Octetos{bs}:
      Unit
    case C.NomeTexto{} Octetos{bs}:
      Unit
    case C.ContaLista{} Valores{xs}:
      S.ValoresCanonicos(xs)
    case C.ContaRegistro{} Campos{xs}:
      S.CamposCanonicos(xs)
    case _ _:
      Empty

law segmento_compativel_exige_minimo_campo_natural:
  for +f: C.Finalidade
  for +s: SegmentoAtual
  for compativel: SegmentoCompativel(f, s)
  {Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}
def segmento_compativel_exige_minimo_campo_natural(f, s, compativel):
  match f s:
    case C.Inteiro{} Octetos{+bs}:
      S.limite_reflexivo(B.comprimento(bs))
    case C.Texto{} Octetos{+bs}:
      S.limite_reflexivo(B.comprimento(bs))
    case C.NomeTexto{} Octetos{+bs}:
      S.limite_reflexivo(B.comprimento(bs))
    case C.ContaLista{} Valores{+xs}:
      S.sequencia_de_valores_canonicos_exige_um_octeto_por_valor(xs, compativel)
    case C.ContaRegistro{} Campos{+xs}:
      S.sequencia_de_campos_canonicos_exige_onze_octetos_por_campo(xs, compativel)
    case C.Inteiro{} Valores{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.Inteiro{} Campos{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.Texto{} Valores{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.Texto{} Campos{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.NomeTexto{} Valores{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.NomeTexto{} Campos{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.ContaLista{} Octetos{bs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.ContaLista{} Campos{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.ContaRegistro{} Octetos{bs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)
    case C.ContaRegistro{} Valores{xs}:
      L.ex_falso({Nat.is_le(G.minimo_campo_natural(f, quantidade_atual(s)), B.comprimento(bytes_atuais(s))) == True{} : Bool}, compativel)

# Corolario para o conferir REAL chamado por concluir_palavra. A unica
# reserva suposta e o corpo medido que contem estes segmentos canonicos.
law campo_e_pilha_canonicos_cabem_no_sufixo_real:
  for +f: C.Finalidade
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +s: SegmentoAtual
  for +plano: Plano
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medido: {B.nat64(quantidade_atual(s)) == Some{q} : Maybe<&2, B.Numero64>}
  for compativel: SegmentoCompativel(f, s)
  for canonico: PlanoCanonico(pilha, plano)
  for corpo_medido: {B.nat64(B.comprimento(B.concatenar(bytes_atuais(s), bytes_pendentes(plano)))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}
def campo_e_pilha_canonicos_cabem_no_sufixo_real(f, q, pilha, s, plano, corpo, teto, medido, compativel, canonico, corpo_medido, cabe):
  F.com_par({C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia},
    {C.minimo_pilha(pilha) == B.nat64(minimo_natural(plano)) : Maybe<&2, B.Numero64>},
    {Nat.is_le(minimo_natural(plano), B.comprimento(bytes_pendentes(plano))) == True{} : Bool},
    minimo_pilha_canonica_e_exato_e_limitado_pelos_bytes_pendentes(pilha, plano, canonico),
    exato => limite => R.conferir_minimo_composto_pelo_corpo_real(f, quantidade_atual(s), minimo_natural(plano), B.comprimento(B.concatenar(bytes_atuais(s), bytes_pendentes(plano))), q, pilha, corpo, teto,
        medido, exato, corpo_medido,
        S.concatenar_segmentos_preserva_soma_dos_limites(bytes_atuais(s), bytes_pendentes(plano), G.minimo_campo_natural(f, quantidade_atual(s)), minimo_natural(plano),
          segmento_compativel_exige_minimo_campo_natural(f, s, compativel), limite), cabe))
