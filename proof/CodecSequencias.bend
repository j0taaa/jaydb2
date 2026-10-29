# Passos indutivos sobre filhos E SEUS SEGMENTOS REAIS de bytes. As
# hipoteses de inducao sao estritamente por filho, sob qualquer pilha e
# sufixo com reserva numerica; nao pressupõem a aceitacao da lista inteira.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecComposicao.bend as X
import ./CodecContadores.bend as N
import ./CodecPalavrasBE64.bend as H
import ./CodecTextos.bend as T
import ./CodecMinimos.bend as M
import ./CodecMinimosPilha.bend as A
import ./CodecCanonico.bend as K
import ./CodecLimitesSequencias.bend as S
import ./CodecLimitesNomes.bend as W
import ./CodecSomasMinimos.bend as J

# A reserva refere-se a bytes de irmaos/ancestrais que REALMENTE seguem o
# segmento. Nao e uma premissa sobre o resultado do decoder nem conferir.
def CompletoLocal(v: D.Valor, +bs: List<&2, U32>) -> Type:
  @corpo: B.Numero64 -> @teto: B.Numero64 -> @pilha: C.Pilha ->
  @sufixo: List<&2, U32> -> @r: Nat ->
  {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>} ->
  {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool} ->
  {B.nat64(B.comprimento(B.concatenar(bs, sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>} ->
  {C.menor_igual64(corpo, teto) == True{} : Bool} ->
  {R.executar(bs, R.Quadro{corpo, teto, C.Tag{pilha}}) == X.depois(bs, corpo, teto, C.emitir(pilha, v)) : R.Quadro}

def valores(xs: List<&2, S.ValorSegmentado>) -> List<&2, D.Valor>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{S.ValorSegmentado{v, bs}, t}:
      Con{v, valores(t)}

def lista(xs: List<&2, S.ValorSegmentado>) -> D.Valor:
  match xs:
    case Nil{}:
      D.VListaVazia{}
    case Con{S.ValorSegmentado{v, bs}, t}:
      D.VLista{v, lista(t)}

# Os limites de todas as caudas sao resultados independentes de
# CodecLimitesSequencias. O callback e a hipotese sobre o SUBVALOR atual.
def InducaoValores(xs: List<&2, S.ValorSegmentado>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.ValorSegmentado{v, bs}, t}:
      L.E<CompletoLocal(v, bs),
        L.E<{Nat.is_le(S.quantidade_valores(t), B.comprimento(S.bytes_valores(t))) == True{} : Bool}, InducaoValores(t)>>

law medida_apos_segmento:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +corpo: B.Numero64
  for medido: {B.nat64(B.comprimento(B.concatenar(a, b))) == Some{corpo} : Maybe<&2, B.Numero64>}
  {B.nat64(B.comprimento(b)) == Some{H.diminuir(B.comprimento(a), corpo)} : Maybe<&2, B.Numero64>}
def medida_apos_segmento(a, b, corpo, medido):
  T.remover_prefixo_da_medida(B.comprimento(a), B.comprimento(b), corpo,
    (%W.comprimento_concatenacao(a, b) : {B.nat64(_) == Some{corpo} : Maybe<&2, B.Numero64>}
      medido))

law depois_de_segmentos_concatenados:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  {X.depois(b, H.diminuir(B.comprimento(a), corpo), H.diminuir(B.comprimento(a), teto), m) == X.depois(B.concatenar(a, b), corpo, teto, m) : R.Quadro}
def depois_de_segmentos_concatenados(a, b, corpo, teto, m):
  %Equal.sym(B.Numero64, H.diminuir(B.comprimento(B.concatenar(a, b)), corpo), H.diminuir(B.comprimento(b), H.diminuir(B.comprimento(a), corpo)), X.diminuir_por_concatenacao(a, b, corpo)) :
    {R.Quadro{H.diminuir(B.comprimento(b), H.diminuir(B.comprimento(a), corpo)), H.diminuir(B.comprimento(b), H.diminuir(B.comprimento(a), teto)), m} == R.Quadro{_, H.diminuir(B.comprimento(B.concatenar(a, b)), teto), m} : R.Quadro}
  %Equal.sym(B.Numero64, H.diminuir(B.comprimento(B.concatenar(a, b)), teto), H.diminuir(B.comprimento(b), H.diminuir(B.comprimento(a), teto)), X.diminuir_por_concatenacao(a, b, teto)) :
    {R.Quadro{H.diminuir(B.comprimento(b), H.diminuir(B.comprimento(a), corpo)), H.diminuir(B.comprimento(b), H.diminuir(B.comprimento(a), teto)), m} == R.Quadro{H.diminuir(B.comprimento(b), H.diminuir(B.comprimento(a), corpo)), _, m} : R.Quadro}
  {==}

def NaoVazia(xs: List<&2, S.ValorSegmentado>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

def somar_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, somar_zero(p))

def minimo_frame_lista(+u: Bool, +q: B.Numero64, -xs: List<&2, D.Valor>, +pai: C.Pilha,
  +n: Nat, +r: Nat,
  medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>},
  minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}) ->
  {C.minimo_pilha(C.Lista{u, q, xs, pai}) == B.nat64(Nat.add(n, r)) : Maybe<&2, B.Numero64>}:
  %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(r), minimo) :
    {C.somar_pendencia(q, 1n, _) == B.nat64(Nat.add(n, r)) : Maybe<&2, B.Numero64>}
  %somar_zero(n) :
    {C.somar_pendencia(q, 1n, B.nat64(r)) == B.nat64(Nat.add(_, r)) : Maybe<&2, B.Numero64>}
  A.somar_pendencia_nat64_exato(n, q, 1n, r, medido)


law compor_dois_segmentos_reais:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for +n: C.Maquina
  for +fim: C.Maquina
  for primeiro: {R.executar(a, R.Quadro{corpo, teto, m}) == X.depois(a, corpo, teto, n) : R.Quadro}
  for segundo: {R.executar(b, X.depois(a, corpo, teto, n)) == X.depois(b, H.diminuir(B.comprimento(a), corpo), H.diminuir(B.comprimento(a), teto), fim) : R.Quadro}
  {R.executar(B.concatenar(a, b), R.Quadro{corpo, teto, m}) == X.depois(B.concatenar(a, b), corpo, teto, fim) : R.Quadro}
def compor_dois_segmentos_reais(a, b, corpo, teto, m, n, fim, primeiro, segundo):
  Equal.trans(R.Quadro,
    R.executar(B.concatenar(a, b), R.Quadro{corpo, teto, m}),
    R.executar(b, R.executar(a, R.Quadro{corpo, teto, m})),
    X.depois(B.concatenar(a, b), corpo, teto, fim),
    R.execucao_de_concatenacao(a, b, R.Quadro{corpo, teto, m}),
    Equal.trans(R.Quadro,
      R.executar(b, R.executar(a, R.Quadro{corpo, teto, m})), R.executar(b, X.depois(a, corpo, teto, n)),
      X.depois(B.concatenar(a, b), corpo, teto, fim),
      Equal.cong(R.Quadro, R.Quadro, q => R.executar(b, q), R.executar(a, R.Quadro{corpo, teto, m}), X.depois(a, corpo, teto, n), primeiro),
      Equal.trans(R.Quadro, R.executar(b, X.depois(a, corpo, teto, n)),
        X.depois(b, H.diminuir(B.comprimento(a), corpo), H.diminuir(B.comprimento(a), teto), fim),
        X.depois(B.concatenar(a, b), corpo, teto, fim), segundo, depois_de_segmentos_concatenados(a, b, corpo, teto, fim))))

def compor_cauda_lista(+t: List<&2, S.ValorSegmentado>, +q: B.Numero64, +v: D.Valor, +bs: List<&2, U32>,
  +invertidos: List<&2, D.Valor>, +pai: C.Pilha, +sufixo: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +contado: {B.nat64(1n+S.quantidade_valores(t)) == Some{q} : Maybe<&2, B.Numero64>},
  +entrada: {B.nat64(B.comprimento(B.concatenar(bs, B.concatenar(S.bytes_valores(t), sufixo)))) == Some{corpo} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(corpo, teto) == True{} : Bool},
  passo: {R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}}}) ==
    X.depois(bs, corpo, teto, C.emitir(C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, v)) : R.Quadro},
  continuar: NaoVazia(t) ->
    {B.nat64(B.comprimento(B.concatenar(S.bytes_valores(t), sufixo))) == Some{H.diminuir(B.comprimento(bs), corpo)} : Maybe<&2, B.Numero64>} ->
    {C.menor_igual64(H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto)) == True{} : Bool} ->
    {R.executar(S.bytes_valores(t), R.Quadro{H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto),
        C.Tag{C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{v, invertidos}, pai}}}) ==
      X.depois(S.bytes_valores(t), H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto), C.emitir(pai, C.montar_lista(Con{v, invertidos}, lista(t)))) : R.Quadro}) ->
  {R.executar(B.concatenar(bs, S.bytes_valores(t)), R.Quadro{corpo, teto, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}}}) ==
    X.depois(B.concatenar(bs, S.bytes_valores(t)), corpo, teto, C.emitir(pai, C.montar_lista(invertidos, D.VLista{v, lista(t)}))) : R.Quadro}:
  match t:
    case Nil{}:
      +ultimo = N.um64_reflete_contagem_natural(1n, q, contado)
      +emissao = {(%Equal.sym(Bool, C.um64(q), True{}, ultimo) :
        {C.emitir(C.Lista{_, C.diminuir64(q), invertidos, pai}, v) == C.emitir(pai, C.montar_lista(invertidos, D.VLista{v, D.VListaVazia{}})) : C.Maquina}
        {==}) : {C.emitir(C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, v) == C.emitir(pai, C.montar_lista(invertidos, D.VLista{v, D.VListaVazia{}})) : C.Maquina}}
      compor_dois_segmentos_reais(bs, Nil{}, corpo, teto, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}},
        C.emitir(C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, v), C.emitir(pai, C.montar_lista(invertidos, D.VLista{v, D.VListaVazia{}})), passo,
        Equal.cong(C.Maquina, R.Quadro, m => X.depois(bs, corpo, teto, m),
          C.emitir(C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, v), C.emitir(pai, C.montar_lista(invertidos, D.VLista{v, D.VListaVazia{}})), emissao))
    case Con{+h, +resto}:
      +ultimo = N.um64_reflete_contagem_natural(2n+S.quantidade_valores(resto), q, contado)
      +emissao = {(%Equal.sym(Bool, C.um64(q), False{}, ultimo) :
        {C.emitir(C.Lista{_, C.diminuir64(q), invertidos, pai}, v) == C.Tag{C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{v, invertidos}, pai}} : C.Maquina}
        {==}) : {C.emitir(C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, v) == C.Tag{C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{v, invertidos}, pai}} : C.Maquina}}
      compor_dois_segmentos_reais(bs, S.bytes_valores(Con{h, resto}), corpo, teto, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}},
        C.Tag{C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{v, invertidos}, pai}}, C.emitir(pai, C.montar_lista(Con{v, invertidos}, lista(Con{h, resto}))),
        Equal.trans(R.Quadro,
          R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}}}),
          X.depois(bs, corpo, teto, C.emitir(C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, v)),
          X.depois(bs, corpo, teto, C.Tag{C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{v, invertidos}, pai}}), passo,
          Equal.cong(C.Maquina, R.Quadro, m => X.depois(bs, corpo, teto, m),
            C.emitir(C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, v), C.Tag{C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{v, invertidos}, pai}}, emissao)),
        continuar(Unit{}, medida_apos_segmento(bs, B.concatenar(S.bytes_valores(Con{h, resto}), sufixo), corpo, entrada), M.diminuir_repetido_preserva_ordem_dos_limites(B.comprimento(bs), corpo, teto, cabe)))

# O codigo abaixo faz a inducao na CAUDA de segmentos, nao na contagem
# declarada. O contador u64 e reconstituido/decrementado por nat64.
law lista_de_segmentos_compoe_execucao_real_dos_filhos:
  for +xs: List<&2, S.ValorSegmentado>
  for +q: B.Numero64
  for +invertidos: List<&2, D.Valor>
  for +pai: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for positivo: NaoVazia(xs)
  for filhos: InducaoValores(xs)
  for +contado: {B.nat64(S.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  for +minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.concatenar(S.bytes_valores(xs), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(S.bytes_valores(xs), R.Quadro{corpo, teto, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}}}) ==
    X.depois(S.bytes_valores(xs), corpo, teto, C.emitir(pai, C.montar_lista(invertidos, lista(xs)))) : R.Quadro}
def lista_de_segmentos_compoe_execucao_real_dos_filhos(xs, q, invertidos, pai, sufixo, r, corpo, teto, positivo, filhos, contado, minimo, reserva, medido, cabe):
  match xs:
    case Nil{}:
      L.ex_falso({R.Quadro{corpo, teto, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}}} == R.Quadro{corpo, teto, C.emitir(pai, C.montar_lista(invertidos, D.VListaVazia{}))} : R.Quadro}, positivo)
    case Con{S.ValorSegmentado{+v, +bs}, +t}:
      match filhos:
        case L.Ambos{atual, L.Ambos{+tamanho, cauda}}:
          +restantes = N.medida_decrementada(S.quantidade_valores(t), q, N.nat64_sucessor_tem_antecessor_exato(S.quantidade_valores(t), q, contado))
          # minimo_campo(ContaLista,q)=q, e minimo_pilha(Lista)=q+pai.
          +reserva_filho = S.concatenar_segmentos_preserva_soma_dos_limites(S.bytes_valores(t), sufixo, S.quantidade_valores(t), r, tamanho, reserva)
          +entrada_filho = {(%K.concatenacao_associativa(bs, S.bytes_valores(t), sufixo) :
              {B.nat64(B.comprimento(_)) == Some{corpo} : Maybe<&2, B.Numero64>}
              medido) : {B.nat64(B.comprimento(B.concatenar(bs, B.concatenar(S.bytes_valores(t), sufixo)))) == Some{corpo} : Maybe<&2, B.Numero64>}}
          # somar_pendencia pode saltar q=0; esta igualdade e provada pelo
          # lema aritmetico, inclusive sem pressupor representabilidade.
          +minimo_lista = minimo_frame_lista(C.um64(q), C.diminuir64(q), invertidos, pai, S.quantidade_valores(t), r, restantes, minimo)
          +passo = atual(corpo, teto, C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}, B.concatenar(S.bytes_valores(t), sufixo), Nat.add(S.quantidade_valores(t), r), minimo_lista, reserva_filho, entrada_filho, cabe)
          compor_cauda_lista(t, q, v, bs, invertidos, pai, sufixo, corpo, teto, contado, entrada_filho, cabe, passo,
            positivo => medida_cauda => cabe_cauda =>
              lista_de_segmentos_compoe_execucao_real_dos_filhos(t, C.diminuir64(q), Con{v, invertidos}, pai, sufixo, r,
                H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto), positivo, cauda, restantes, minimo, reserva, medida_cauda, cabe_cauda))

law lista_aberta_compoe_todos_os_segmentos:
  for +xs: List<&2, S.ValorSegmentado>
  for +q: B.Numero64
  for +pai: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for filhos: InducaoValores(xs)
  for +contado: {B.nat64(S.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  for +minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.concatenar(S.bytes_valores(xs), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(S.bytes_valores(xs), R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, pai)}) ==
    X.depois(S.bytes_valores(xs), corpo, teto, C.emitir(pai, lista(xs))) : R.Quadro}
def lista_aberta_compoe_todos_os_segmentos(xs, q, pai, sufixo, r, corpo, teto, filhos, contado, minimo, reserva, medido, cabe):
  match xs:
    case Nil{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, q, contado) :
        {R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(_), C.ContaLista{}, q, pai)} == X.depois(Nil{}, corpo, teto, C.emitir(pai, D.VListaVazia{})) : R.Quadro}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(S.quantidade_valores(Con{h, t}), q, contado)) :
        {R.executar(S.bytes_valores(Con{h, t}), R.Quadro{corpo, teto, C.abrir_variavel(_, C.ContaLista{}, q, pai)}) == X.depois(S.bytes_valores(Con{h, t}), corpo, teto, C.emitir(pai, lista(Con{h, t}))) : R.Quadro}
      lista_de_segmentos_compoe_execucao_real_dos_filhos(Con{h, t}, q, Nil{}, pai, sufixo, r, corpo, teto, Unit{}, filhos, contado, minimo, reserva, medido, cabe)

def bytes_lista(alto: U32, baixo: U32, xs: List<&2, S.ValorSegmentado>) -> List<&2, U32>:
  Con{5, B.concatenar(B.be64(alto, baixo), S.bytes_valores(xs))}

# Este e o PASSO DE INDUCAO do construtor lista. Todos os valores dos
# filhos sao arbitrarios; a hipotese recai apenas em cada subvalor menor.
# O unico limite e o corpo/teto real, sem quota de profundidade ou aridade.
law construtor_lista_compoe_completude_local:
  for +xs: List<&2, S.ValorSegmentado>
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pai: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for filhos: InducaoValores(xs)
  for canonicos: S.ValoresCanonicos(xs)
  for +contado: {B.nat64(S.quantidade_valores(xs)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for +minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.concatenar(bytes_lista(alto, baixo, xs), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(bytes_lista(alto, baixo, xs), R.Quadro{corpo, teto, C.Tag{pai}}) ==
    X.depois(bytes_lista(alto, baixo, xs), corpo, teto, C.emitir(pai, lista(xs))) : R.Quadro}
def construtor_lista_compoe_completude_local(xs, alto, baixo, corpo, teto, pai, sufixo, r, filhos, canonicos, contado, minimo, reserva, medido, cabe):
  +medida_cauda = T.remover_prefixo_da_medida(9n, B.comprimento(B.concatenar(S.bytes_valores(xs), sufixo)), corpo, medido)
  +limite_minimo = S.concatenar_segmentos_preserva_soma_dos_limites(S.bytes_valores(xs), sufixo, S.quantidade_valores(xs), r,
    S.sequencia_de_valores_canonicos_exige_um_octeto_por_valor(xs, canonicos), reserva)
  +abertura = X.cabecalho_variavel_com_corpo_e_teto_u64_arbitrario(C.ContaLista{}, S.quantidade_valores(xs), r, B.comprimento(B.concatenar(S.bytes_valores(xs), sufixo)), alto, baixo, pai, corpo, teto, Unit{}, contado, minimo, medida_cauda, limite_minimo, cabe)
  compor_dois_segmentos_reais(Con{5, B.be64(alto, baixo)}, S.bytes_valores(xs), corpo, teto, C.Tag{pai},
    C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.ContaLista{}, B.Numero64{alto, baixo}, pai), C.emitir(pai, lista(xs)), abertura,
    lista_aberta_compoe_todos_os_segmentos(xs, B.Numero64{alto, baixo}, pai, sufixo, r, H.diminuir(9n, corpo), H.diminuir(9n, teto), filhos, contado, minimo, reserva, medida_cauda,
      M.diminuir_repetido_preserva_ordem_dos_limites(9n, corpo, teto, cabe)))
