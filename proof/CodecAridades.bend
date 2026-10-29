# Reconstrucao estrutural exata das aridades declaradas. O parametro Nat
# e o comprimento matematico da sequencia de filhos, sem limite adicional.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecContadores.bend as N

def proximo_valor(m: C.Maquina, v: D.Valor) -> C.Maquina:
  match m:
    case C.Tag{pilha}:
      C.emitir(pilha, v)
    case _:
      C.Invalido{}

def entregar_valores(xs: List<&2, D.Valor>, m: C.Maquina) -> C.Maquina:
  match xs:
    case Nil{}:
      m
    case Con{v, t}:
      entregar_valores(t, proximo_valor(m, v))

def quantidade_valores(xs: List<&2, D.Valor>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+quantidade_valores(t)

def anexar_lista(xs: List<&2, D.Valor>, acc: D.Valor) -> D.Valor:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      D.VLista{h, anexar_lista(t, acc)}

def ValoresNaoVazios(xs: List<&2, D.Valor>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

law lista_contada_reconstroi_exatamente_todos_os_filhos:
  for +xs: List<&2, D.Valor>
  for +q: B.Numero64
  for +invertidos: List<&2, D.Valor>
  for +pai: C.Pilha
  for positivo: ValoresNaoVazios(xs)
  for +medido: {B.nat64(quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  {entregar_valores(xs, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}}) ==
    C.emitir(pai, C.montar_lista(invertidos, anexar_lista(xs, D.VListaVazia{}))) : C.Maquina}
def lista_contada_reconstroi_exatamente_todos_os_filhos(xs, q, invertidos, pai, positivo, medido):
  match xs:
    case Nil{}:
      L.ex_falso({C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, pai}} == C.emitir(pai, C.montar_lista(invertidos, D.VListaVazia{})) : C.Maquina}, positivo)
    case Con{+h, Nil{}}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 1}, q, medido) :
        {entregar_valores(Con{h, Nil{}}, C.Tag{C.Lista{C.um64(_), C.diminuir64(q), invertidos, pai}}) ==
          C.emitir(pai, C.montar_lista(invertidos, D.VLista{h, D.VListaVazia{}})) : C.Maquina}
      {==}
    case Con{+h, Con{+v, +resto}}:
      +t = {Con{v, resto} : List<&2, D.Valor>}
      %Equal.sym(Bool, C.um64(q), False{}, N.um64_reflete_contagem_natural(quantidade_valores(Con{h, t}), q, medido)) :
        {entregar_valores(t, C.emitir(C.Lista{_, C.diminuir64(q), invertidos, pai}, h)) ==
          C.emitir(pai, C.montar_lista(invertidos, D.VLista{h, anexar_lista(t, D.VListaVazia{})})) : C.Maquina}
      lista_contada_reconstroi_exatamente_todos_os_filhos(t, C.diminuir64(q), Con{h, invertidos}, pai, Unit{},
        N.medida_decrementada(quantidade_valores(t), q, N.nat64_sucessor_tem_antecessor_exato(quantidade_valores(t), q, medido)))

law abertura_de_lista_contada_preserva_aridade_e_ordem:
  for +xs: List<&2, D.Valor>
  for +q: B.Numero64
  for +pai: C.Pilha
  for +medido: {B.nat64(quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  {entregar_valores(xs, C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, pai)) ==
    C.emitir(pai, anexar_lista(xs, D.VListaVazia{})) : C.Maquina}
def abertura_de_lista_contada_preserva_aridade_e_ordem(xs, q, pai, medido):
  match xs:
    case Nil{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, q, medido) :
        {C.abrir_variavel(C.zero64(_), C.ContaLista{}, q, pai) == C.emitir(pai, D.VListaVazia{}) : C.Maquina}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(quantidade_valores(Con{h, t}), q, medido)) :
        {entregar_valores(Con{h, t}, C.abrir_variavel(_, C.ContaLista{}, q, pai)) == C.emitir(pai, anexar_lista(Con{h, t}, D.VListaVazia{})) : C.Maquina}
      lista_contada_reconstroi_exatamente_todos_os_filhos(Con{h, t}, q, Nil{}, pai, Unit{}, medido)

# Campos entregues na ordem de leitura. A ordem estrita e o predicado real
# de nomes do contrato sao verificados antes de inserir cada valor.
def CamposOrdenados(xs: List<&2, D.Campo>, anterior: String) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Campo{n, v}, t}:
      L.E<{D.nome_valido(n) == True{} : Bool},
        L.E<{String.is_lt(anterior, n) == True{} : Bool}, CamposOrdenados(t, n)>>

def quantidade_campos(xs: List<&2, D.Campo>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+quantidade_campos(t)

def anexar_registro(xs: List<&2, D.Campo>, acc: D.Valor) -> D.Valor:
  match xs:
    case Nil{}:
      acc
    case Con{D.Campo{n, v}, t}:
      D.VRegistro{n, v, anexar_registro(t, acc)}

def entregar_campo(m: C.Maquina, campo: D.Campo) -> C.Maquina:
  match m campo:
    case C.TagNome{pilha} D.Campo{n, v}:
      proximo_valor(C.emitir_nome(pilha, n), v)
    case _ _:
      C.Invalido{}

def entregar_campos(xs: List<&2, D.Campo>, m: C.Maquina) -> C.Maquina:
  match xs:
    case Nil{}:
      m
    case Con{h, t}:
      entregar_campos(t, entregar_campo(m, h))

def CamposNaoVazios(xs: List<&2, D.Campo>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

law campo_ordenado_e_entregue_sem_troca:
  for +ultimo: Bool
  for +q: B.Numero64
  for +anterior: String
  for +nome: String
  for +v: D.Valor
  for +invertidos: List<&2, D.Campo>
  for +pai: C.Pilha
  for nome_valido: {D.nome_valido(nome) == True{} : Bool}
  for ordem: {String.is_lt(anterior, nome) == True{} : Bool}
  {entregar_campo(C.TagNome{C.Nome{ultimo, q, anterior, invertidos, pai}}, D.Campo{nome, v}) ==
    C.emitir(C.Campo{ultimo, q, nome, invertidos, pai}, v) : C.Maquina}
def campo_ordenado_e_entregue_sem_troca(ultimo, q, anterior, nome, v, invertidos, pai, nome_valido, ordem):
  %Equal.sym(Bool, D.nome_valido(nome) && String.is_lt(anterior, nome), True{},
    F.e_booleano_intro(D.nome_valido(nome), String.is_lt(anterior, nome), nome_valido, ordem)) :
    {proximo_valor(C.nome_conferido(_, ultimo, q, nome, invertidos, pai), v) == C.emitir(C.Campo{ultimo, q, nome, invertidos, pai}, v) : C.Maquina}
  {==}

# A hipotese indutiva e aplicada depois de conferir o nome do campo atual.
def continuar_campos(+xs: List<&2, D.Campo>, +q: B.Numero64,
  +anterior: String, +nome: String, +v: D.Valor,
  +invertidos: List<&2, D.Campo>, +pai: C.Pilha,
  nome_valido: {D.nome_valido(nome) == True{} : Bool},
  ordem: {String.is_lt(anterior, nome) == True{} : Bool},
  ultimo: Bool) ->
  {entregar_campos(xs, entregar_campo(C.TagNome{C.Nome{ultimo, q, anterior, invertidos, pai}}, D.Campo{nome, v})) ==
    entregar_campos(xs, C.emitir(C.Campo{ultimo, q, nome, invertidos, pai}, v)) : C.Maquina}:
  Equal.cong(C.Maquina, C.Maquina, m => entregar_campos(xs, m),
    entregar_campo(C.TagNome{C.Nome{ultimo, q, anterior, invertidos, pai}}, D.Campo{nome, v}),
    C.emitir(C.Campo{ultimo, q, nome, invertidos, pai}, v),
    campo_ordenado_e_entregue_sem_troca(ultimo, q, anterior, nome, v, invertidos, pai, nome_valido, ordem))

law registro_contado_reconstroi_exatamente_todos_os_campos:
  for +xs: List<&2, D.Campo>
  for +q: B.Numero64
  for +anterior: String
  for +invertidos: List<&2, D.Campo>
  for +pai: C.Pilha
  for positivo: CamposNaoVazios(xs)
  for ordenados: CamposOrdenados(xs, anterior)
  for +medido: {B.nat64(quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  {entregar_campos(xs, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}}) ==
    C.emitir(pai, C.montar_registro(invertidos, anexar_registro(xs, D.VRegistroVazio{}))) : C.Maquina}
def registro_contado_reconstroi_exatamente_todos_os_campos(xs, q, anterior, invertidos, pai, positivo, ordenados, medido):
  match xs:
    case Nil{}:
      L.ex_falso({C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}} == C.emitir(pai, C.montar_registro(invertidos, D.VRegistroVazio{})) : C.Maquina}, positivo)
    case Con{D.Campo{+nome, +v}, Nil{}}:
      match ordenados:
        case L.Ambos{nome_valido, L.Ambos{ordem, cauda}}:
          %F.algum_injetivo(B.Numero64, B.Numero64{0, 1}, q, medido) :
            {entregar_campo(C.TagNome{C.Nome{C.um64(_), C.diminuir64(q), anterior, invertidos, pai}}, D.Campo{nome, v}) ==
              C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, D.VRegistroVazio{}})) : C.Maquina}
          campo_ordenado_e_entregue_sem_troca(True{}, C.diminuir64(q), anterior, nome, v, invertidos, pai, nome_valido, ordem)
    case Con{D.Campo{+nome, +v}, Con{+campo, +resto}}:
      match ordenados:
        case L.Ambos{nome_valido, L.Ambos{ordem, cauda}}:
          +t = {Con{campo, resto} : List<&2, D.Campo>}
          %Equal.sym(Bool, C.um64(q), False{}, N.um64_reflete_contagem_natural(quantidade_campos(xs), q, medido)) :
            {entregar_campos(t, entregar_campo(C.TagNome{C.Nome{_, C.diminuir64(q), anterior, invertidos, pai}}, D.Campo{nome, v})) ==
              C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, anexar_registro(t, D.VRegistroVazio{})})) : C.Maquina}
          Equal.trans(C.Maquina,
            entregar_campos(t, entregar_campo(C.TagNome{C.Nome{False{}, C.diminuir64(q), anterior, invertidos, pai}}, D.Campo{nome, v})),
            entregar_campos(t, C.emitir(C.Campo{False{}, C.diminuir64(q), nome, invertidos, pai}, v)),
            C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, anexar_registro(t, D.VRegistroVazio{})})),
            continuar_campos(t, C.diminuir64(q), anterior, nome, v, invertidos, pai, nome_valido, ordem, False{}),
            registro_contado_reconstroi_exatamente_todos_os_campos(t, C.diminuir64(q), nome, Con{D.Campo{nome, v}, invertidos}, pai, Unit{}, cauda,
              N.medida_decrementada(quantidade_campos(t), q, N.nat64_sucessor_tem_antecessor_exato(quantidade_campos(t), q, medido))))

law abertura_de_registro_contado_preserva_aridade_e_ordem:
  for +xs: List<&2, D.Campo>
  for +q: B.Numero64
  for +pai: C.Pilha
  for ordenados: CamposOrdenados(xs, "")
  for +medido: {B.nat64(quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  {entregar_campos(xs, C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, pai)) ==
    C.emitir(pai, anexar_registro(xs, D.VRegistroVazio{})) : C.Maquina}
def abertura_de_registro_contado_preserva_aridade_e_ordem(xs, q, pai, ordenados, medido):
  match xs:
    case Nil{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, q, medido) :
        {C.abrir_variavel(C.zero64(_), C.ContaRegistro{}, q, pai) == C.emitir(pai, D.VRegistroVazio{}) : C.Maquina}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(quantidade_campos(Con{h, t}), q, medido)) :
        {entregar_campos(Con{h, t}, C.abrir_variavel(_, C.ContaRegistro{}, q, pai)) == C.emitir(pai, anexar_registro(Con{h, t}, D.VRegistroVazio{})) : C.Maquina}
      registro_contado_reconstroi_exatamente_todos_os_campos(Con{h, t}, q, "", Nil{}, pai, Unit{}, ordenados, medido)

def pronta(m: C.Maquina) -> Bool:
  match m:
    case C.Pronto{v}:
      True{}
    case _:
      False{}

law tag_nao_e_pronto:
  for -pilha: C.Pilha
  for -v: D.Valor
  for e: {C.Tag{pilha} == C.Pronto{v} : C.Maquina}
  Empty
def tag_nao_e_pronto(pilha, v, e):
  F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => pronta(m), C.Tag{pilha}, C.Pronto{v}, e))

law invalido_nao_e_pronto:
  for -v: D.Valor
  for e: {C.Invalido{} == C.Pronto{v} : C.Maquina}
  Empty
def invalido_nao_e_pronto(v, e):
  F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => pronta(m), C.Invalido{}, C.Pronto{v}, e))

law valores_nao_recuperam_maquina_invalida:
  for xs: List<&2, D.Valor>
  {entregar_valores(xs, C.Invalido{}) == C.Invalido{} : C.Maquina}
def valores_nao_recuperam_maquina_invalida(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      valores_nao_recuperam_maquina_invalida(t)

law pronto_recusa_valor_extra:
  for h: D.Valor
  for xs: List<&2, D.Valor>
  for v: D.Valor
  {entregar_valores(Con{h, xs}, C.Pronto{v}) == C.Invalido{} : C.Maquina}
def pronto_recusa_valor_extra(h, xs, v):
  valores_nao_recuperam_maquina_invalida(xs)

def conferir_filho_unico(ultimo: Bool, +q: B.Numero64, +h: D.Valor,
  +invertidos: List<&2, D.Valor>, -v: D.Valor,
  aceito: {C.emitir(C.Lista{ultimo, C.diminuir64(q), invertidos, C.Raiz{}}, h) == C.Pronto{v} : C.Maquina}) ->
  {ultimo == True{} : Bool}:
  match ultimo:
    case True{}:
      {==}
    case False{}:
      L.ex_falso({False{} == True{} : Bool},
        tag_nao_e_pronto(C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{h, invertidos}, C.Raiz{}}, v, aceito))

# Hipotese estrutural sobre a cauda fornecida pela inducao abaixo.
def conferir_filhos_restantes(ultimo: Bool, +q: B.Numero64, +h: D.Valor,
  +x: D.Valor, +xs: List<&2, D.Valor>, +invertidos: List<&2, D.Valor>, -v: D.Valor,
  aceito: {entregar_valores(Con{x, xs}, C.emitir(C.Lista{ultimo, C.diminuir64(q), invertidos, C.Raiz{}}, h)) == C.Pronto{v} : C.Maquina},
  continuar: {entregar_valores(Con{x, xs}, C.Tag{C.Lista{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), Con{h, invertidos}, C.Raiz{}}}) == C.Pronto{v} : C.Maquina} ->
    {N.ultimos(quantidade_valores(Con{x, xs}), C.diminuir64(q)) == True{} : Bool}) ->
  {Bool.not(ultimo) && N.ultimos(quantidade_valores(Con{x, xs}), C.diminuir64(q)) == True{} : Bool}:
  match ultimo:
    case False{}:
      continuar(aceito)
    case True{}:
      L.ex_falso({False{} == True{} : Bool}, invalido_nao_e_pronto(v,
        Equal.trans(C.Maquina, C.Invalido{}, entregar_valores(Con{x, xs}, C.Pronto{C.montar_lista(Con{h, invertidos}, D.VListaVazia{})}), C.Pronto{v},
          Equal.sym(C.Maquina, entregar_valores(Con{x, xs}, C.Pronto{C.montar_lista(Con{h, invertidos}, D.VListaVazia{})}), C.Invalido{},
            pronto_recusa_valor_extra(x, xs, C.montar_lista(Con{h, invertidos}, D.VListaVazia{}))), aceito)))

law lista_fechada_conferiu_exatamente_todos_os_ultimos:
  for +xs: List<&2, D.Valor>
  for +q: B.Numero64
  for +invertidos: List<&2, D.Valor>
  for -v: D.Valor
  for aceito: {entregar_valores(xs, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, C.Raiz{}}}) == C.Pronto{v} : C.Maquina}
  {N.ultimos(quantidade_valores(xs), q) == True{} : Bool}
def lista_fechada_conferiu_exatamente_todos_os_ultimos(xs, q, invertidos, v, aceito):
  match xs:
    case Nil{}:
      L.ex_falso({False{} == True{} : Bool}, tag_nao_e_pronto(C.Lista{C.um64(q), C.diminuir64(q), invertidos, C.Raiz{}}, v, aceito))
    case Con{h, Nil{}}:
      conferir_filho_unico(C.um64(q), q, h, invertidos, v, aceito)
    case Con{+h, Con{+x, +resto}}:
      conferir_filhos_restantes(C.um64(q), q, h, x, resto, invertidos, v, aceito,
        e => lista_fechada_conferiu_exatamente_todos_os_ultimos(Con{x, resto}, C.diminuir64(q), Con{h, invertidos}, v, e))

law lista_fechada_reconstroi_a_contagem_canonica_original:
  for +xs: List<&2, D.Valor>
  for +q: B.Numero64
  for +invertidos: List<&2, D.Valor>
  for -v: D.Valor
  for aceito: {entregar_valores(xs, C.Tag{C.Lista{C.um64(q), C.diminuir64(q), invertidos, C.Raiz{}}}) == C.Pronto{v} : C.Maquina}
  {B.nat64(quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}
def lista_fechada_reconstroi_a_contagem_canonica_original(xs, q, invertidos, v, aceito):
  N.ultimos_aceitos_reconstroem_a_contagem_original(quantidade_valores(xs), q,
    lista_fechada_conferiu_exatamente_todos_os_ultimos(xs, q, invertidos, v, aceito))

law tag_nome_nao_e_pronto:
  for -pilha: C.Pilha
  for -v: D.Valor
  for e: {C.TagNome{pilha} == C.Pronto{v} : C.Maquina}
  Empty
def tag_nome_nao_e_pronto(pilha, v, e):
  F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => pronta(m), C.TagNome{pilha}, C.Pronto{v}, e))

law campos_nao_recuperam_maquina_invalida:
  for xs: List<&2, D.Campo>
  {entregar_campos(xs, C.Invalido{}) == C.Invalido{} : C.Maquina}
def campos_nao_recuperam_maquina_invalida(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      campos_nao_recuperam_maquina_invalida(t)

law pronto_recusa_campo_extra:
  for h: D.Campo
  for xs: List<&2, D.Campo>
  for v: D.Valor
  {entregar_campos(Con{h, xs}, C.Pronto{v}) == C.Invalido{} : C.Maquina}
def pronto_recusa_campo_extra(h, xs, v):
  campos_nao_recuperam_maquina_invalida(xs)

def campo_unico_confere_ultimo(ok: Bool, ultimo: Bool, +q: B.Numero64,
  +nome: String, +valor: D.Valor, +invertidos: List<&2, D.Campo>, -v: D.Valor,
  aceito: {proximo_valor(C.nome_conferido(ok, ultimo, C.diminuir64(q), nome, invertidos, C.Raiz{}), valor) == C.Pronto{v} : C.Maquina}) ->
  {ultimo == True{} : Bool}:
  match ok ultimo:
    case False{} _:
      L.ex_falso({ultimo == True{} : Bool}, invalido_nao_e_pronto(v, aceito))
    case True{} True{}:
      {==}
    case True{} False{}:
      L.ex_falso({False{} == True{} : Bool}, tag_nome_nao_e_pronto(C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, valor}, invertidos}, C.Raiz{}}, v, aceito))

def campos_restantes_conferem_ultimo(ok: Bool, ultimo: Bool, +q: B.Numero64,
  +nome: String, +valor: D.Valor, +h: D.Campo, +xs: List<&2, D.Campo>, +invertidos: List<&2, D.Campo>, -v: D.Valor,
  aceito: {entregar_campos(Con{h, xs}, proximo_valor(C.nome_conferido(ok, ultimo, C.diminuir64(q), nome, invertidos, C.Raiz{}), valor)) == C.Pronto{v} : C.Maquina},
  continuar: {entregar_campos(Con{h, xs}, C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, valor}, invertidos}, C.Raiz{}}}) == C.Pronto{v} : C.Maquina} ->
    {N.ultimos(quantidade_campos(Con{h, xs}), C.diminuir64(q)) == True{} : Bool}) ->
  {Bool.not(ultimo) && N.ultimos(quantidade_campos(Con{h, xs}), C.diminuir64(q)) == True{} : Bool}:
  match ok ultimo:
    case False{} _:
      L.ex_falso({Bool.not(ultimo) && N.ultimos(quantidade_campos(Con{h, xs}), C.diminuir64(q)) == True{} : Bool}, invalido_nao_e_pronto(v,
        Equal.trans(C.Maquina, C.Invalido{}, entregar_campos(Con{h, xs}, C.Invalido{}), C.Pronto{v},
          Equal.sym(C.Maquina, entregar_campos(Con{h, xs}, C.Invalido{}), C.Invalido{}, campos_nao_recuperam_maquina_invalida(Con{h, xs})), aceito)))
    case True{} False{}:
      continuar(aceito)
    case True{} True{}:
      L.ex_falso({False{} == True{} : Bool}, invalido_nao_e_pronto(v,
        Equal.trans(C.Maquina, C.Invalido{}, entregar_campos(Con{h, xs}, C.Pronto{C.montar_registro(Con{D.Campo{nome, valor}, invertidos}, D.VRegistroVazio{})}), C.Pronto{v},
          Equal.sym(C.Maquina, entregar_campos(Con{h, xs}, C.Pronto{C.montar_registro(Con{D.Campo{nome, valor}, invertidos}, D.VRegistroVazio{})}), C.Invalido{},
            pronto_recusa_campo_extra(h, xs, C.montar_registro(Con{D.Campo{nome, valor}, invertidos}, D.VRegistroVazio{}))), aceito)))

law registro_fechado_conferiu_exatamente_todos_os_ultimos:
  for +xs: List<&2, D.Campo>
  for +q: B.Numero64
  for +anterior: String
  for +invertidos: List<&2, D.Campo>
  for -v: D.Valor
  for aceito: {entregar_campos(xs, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, C.Raiz{}}}) == C.Pronto{v} : C.Maquina}
  {N.ultimos(quantidade_campos(xs), q) == True{} : Bool}
def registro_fechado_conferiu_exatamente_todos_os_ultimos(xs, q, anterior, invertidos, v, aceito):
  match xs:
    case Nil{}:
      L.ex_falso({False{} == True{} : Bool}, tag_nome_nao_e_pronto(C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, C.Raiz{}}, v, aceito))
    case Con{D.Campo{+nome, +valor}, Nil{}}:
      campo_unico_confere_ultimo(D.nome_valido(nome) && String.is_lt(anterior, nome), C.um64(q), q, nome, valor, invertidos, v, aceito)
    case Con{D.Campo{+nome, +valor}, Con{+h, +t}}:
      campos_restantes_conferem_ultimo(D.nome_valido(nome) && String.is_lt(anterior, nome), C.um64(q), q, nome, valor, h, t, invertidos, v, aceito,
        e => registro_fechado_conferiu_exatamente_todos_os_ultimos(Con{h, t}, C.diminuir64(q), nome, Con{D.Campo{nome, valor}, invertidos}, v, e))

law registro_fechado_reconstroi_a_contagem_canonica_original:
  for +xs: List<&2, D.Campo>
  for +q: B.Numero64
  for +anterior: String
  for +invertidos: List<&2, D.Campo>
  for -v: D.Valor
  for aceito: {entregar_campos(xs, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, C.Raiz{}}}) == C.Pronto{v} : C.Maquina}
  {B.nat64(quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}
def registro_fechado_reconstroi_a_contagem_canonica_original(xs, q, anterior, invertidos, v, aceito):
  N.ultimos_aceitos_reconstroem_a_contagem_original(quantidade_campos(xs), q,
    registro_fechado_conferiu_exatamente_todos_os_ultimos(xs, q, anterior, invertidos, v, aceito))
