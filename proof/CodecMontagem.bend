# Ponte canonica entre segmentos originais dos filhos e os containers.
# Reutiliza os segmentos de CodecLimitesSequencias, em ordem de leitura.
# Nenhuma hipotese afirma a codificacao do container inteiro.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecAridades.bend as A
import ./CodecCanonico.bend as K
import ./CodecLimitesSequencias.bend as S

def prefixo(tag: U32, q: B.Numero64, bs: List<&2, U32>) -> List<&2, U32>:
  B.Numero64{alto, baixo} = q
  Con{tag, B.concatenar(B.be64(alto, baixo), bs)}

law quantidade_valores_projetados:
  for xs: List<&2, S.ValorSegmentado>
  {A.quantidade_valores(S.valores(xs)) == S.quantidade_valores(xs) : Nat}
def quantidade_valores_projetados(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.ValorSegmentado{v, bs}, t}:
      Equal.cong(Nat, Nat, n => 1n+n,
        A.quantidade_valores(S.valores(t)), S.quantidade_valores(t), quantidade_valores_projetados(t))

law quantidade_campos_projetados:
  for xs: List<&2, S.CampoSegmentado>
  {A.quantidade_campos(S.campos(xs)) == S.quantidade_campos(xs) : Nat}
def quantidade_campos_projetados(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.CampoSegmentado{n, v, nb, vb}, t}:
      Equal.cong(Nat, Nat, n => 1n+n,
        A.quantidade_campos(S.campos(t)), S.quantidade_campos(t), quantidade_campos_projetados(t))

def separar_codificacao(valido: Bool, +resultado: Maybe<&2, List<&2, U32>>,
  +bs: List<&2, U32>, aceito: {P.codificar_casos(valido, resultado) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  L.E<{valido == True{} : Bool}, {resultado == Some{bs} : Maybe<&2, List<&2, U32>>}>:
  match valido:
    case False{}:
      L.ex_falso(L.E<{False{} == True{} : Bool}, {resultado == Some{bs} : Maybe<&2, List<&2, U32>>}>,
        F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case True{}:
      L.Ambos{{==}, aceito}

law filho_canonico_expoe_validade_e_bytes:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for canonico: P.Codificacao(v, bs)
  L.E<{D.valor_valido(v) == True{} : Bool},
    {P.finalizar(P.codificar_parcial(v)) == Some{bs} : Maybe<&2, List<&2, U32>>}>
def filho_canonico_expoe_validade_e_bytes(v, bs, canonico):
  separar_codificacao(D.valor_valido(v), P.finalizar(P.codificar_parcial(v)), bs, canonico)

law anexar_lista_tem_forma_de_lista:
  for xs: List<&2, D.Valor>
  {D.eh_lista(A.anexar_lista(xs, D.VListaVazia{})) == True{} : Bool}
def anexar_lista_tem_forma_de_lista(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

law lista_segmentada_preserva_validade_e_parcial:
  for +xs: List<&2, S.ValorSegmentado>
  for canonicos: S.ValoresCanonicos(xs)
  L.E<{D.valor_valido(A.anexar_lista(S.valores(xs), D.VListaVazia{})) == True{} : Bool},
    {P.codificar_parcial(A.anexar_lista(S.valores(xs), D.VListaVazia{})) ==
      P.Lista{S.quantidade_valores(xs), S.bytes_valores(xs)} : P.Parcial}>
def lista_segmentada_preserva_validade_e_parcial(xs, canonicos):
  match xs:
    case Nil{}:
      L.Ambos{{==}, {==}}
    case Con{S.ValorSegmentado{+h, +bs}, +t}:
      match canonicos:
        case L.Ambos{cabeca, cauda}:
          F.com_par(
            L.E<{D.valor_valido(A.anexar_lista(S.valores(xs), D.VListaVazia{})) == True{} : Bool},
              {P.codificar_parcial(A.anexar_lista(S.valores(xs), D.VListaVazia{})) == P.Lista{S.quantidade_valores(xs), S.bytes_valores(xs)} : P.Parcial}>,
            {D.valor_valido(h) == True{} : Bool},
            {P.finalizar(P.codificar_parcial(h)) == Some{bs} : Maybe<&2, List<&2, U32>>},
            filho_canonico_expoe_validade_e_bytes(h, bs, cabeca),
            valido => bytes =>
              F.com_par(
                L.E<{D.valor_valido(A.anexar_lista(S.valores(xs), D.VListaVazia{})) == True{} : Bool},
                  {P.codificar_parcial(A.anexar_lista(S.valores(xs), D.VListaVazia{})) == P.Lista{S.quantidade_valores(xs), S.bytes_valores(xs)} : P.Parcial}>,
                {D.valor_valido(A.anexar_lista(S.valores(t), D.VListaVazia{})) == True{} : Bool},
                {P.codificar_parcial(A.anexar_lista(S.valores(t), D.VListaVazia{})) == P.Lista{S.quantidade_valores(t), S.bytes_valores(t)} : P.Parcial},
                lista_segmentada_preserva_validade_e_parcial(t, cauda),
                resto_valido => resto_bytes => L.Ambos{
                  F.e_booleano_intro(D.valor_valido(h) && D.eh_lista(A.anexar_lista(S.valores(t), D.VListaVazia{})),
                    D.valor_valido(A.anexar_lista(S.valores(t), D.VListaVazia{})),
                    F.e_booleano_intro(D.valor_valido(h), D.eh_lista(A.anexar_lista(S.valores(t), D.VListaVazia{})),
                      valido, anexar_lista_tem_forma_de_lista(S.valores(t))), resto_valido),
                  (%Equal.sym(Maybe<&2, List<&2, U32>>, P.finalizar(P.codificar_parcial(h)), Some{bs}, bytes) :
                    {P.lista_casos(_, P.codificar_parcial(A.anexar_lista(S.valores(t), D.VListaVazia{}))) == P.Lista{S.quantidade_valores(xs), S.bytes_valores(xs)} : P.Parcial}
                    %Equal.sym(P.Parcial, P.codificar_parcial(A.anexar_lista(S.valores(t), D.VListaVazia{})), P.Lista{S.quantidade_valores(t), S.bytes_valores(t)}, resto_bytes) :
                      {P.lista_casos(Some{bs}, _) == P.Lista{S.quantidade_valores(xs), S.bytes_valores(xs)} : P.Parcial}
                    {==})}))

# A primeira igualdade e a fronteira estrita exigida pelo registro pai.
def RegistroMontado(+xs: List<&2, S.CampoSegmentado>, anterior: String) -> Type:
  L.E<{D.registro_depois(A.anexar_registro(S.campos(xs), D.VRegistroVazio{}), anterior) == True{} : Bool},
    L.E<{D.valor_valido(A.anexar_registro(S.campos(xs), D.VRegistroVazio{})) == True{} : Bool},
      {P.codificar_parcial(A.anexar_registro(S.campos(xs), D.VRegistroVazio{})) ==
        P.Registro{S.quantidade_campos(xs), S.bytes_campos(xs)} : P.Parcial}>>

def juntar_cabeca_registro(+n: String, +v: D.Valor, +nb: List<&2, U32>, +vb: List<&2, U32>,
  +t: List<&2, S.CampoSegmentado>, +anterior: String,
  nome: {D.nome_valido(n) == True{} : Bool}, ordem: {String.is_lt(anterior, n) == True{} : Bool},
  nome_bytes: {P.texto(n) == Some{nb} : Maybe<&2, List<&2, U32>>},
  filho: L.E<{D.valor_valido(v) == True{} : Bool}, {P.finalizar(P.codificar_parcial(v)) == Some{vb} : Maybe<&2, List<&2, U32>>}>,
  resto: RegistroMontado(t, n)) -> RegistroMontado(Con{S.CampoSegmentado{n, v, nb, vb}, t}, anterior):
  match filho resto:
    case L.Ambos{valido, bytes} L.Ambos{fronteira, L.Ambos{resto_valido, resto_bytes}}:
      +xs = {Con{S.CampoSegmentado{n, v, nb, vb}, t} : List<&2, S.CampoSegmentado>}
      L.Ambos{ordem, L.Ambos{
        F.e_booleano_intro(D.nome_valido(n) && D.valor_valido(v) && D.registro_depois(A.anexar_registro(S.campos(t), D.VRegistroVazio{}), n),
          D.valor_valido(A.anexar_registro(S.campos(t), D.VRegistroVazio{})),
          F.e_booleano_intro(D.nome_valido(n) && D.valor_valido(v), D.registro_depois(A.anexar_registro(S.campos(t), D.VRegistroVazio{}), n),
            F.e_booleano_intro(D.nome_valido(n), D.valor_valido(v), nome, valido), fronteira), resto_valido),
        (%Equal.sym(Maybe<&2, List<&2, U32>>, P.texto(n), Some{nb}, nome_bytes) :
          {P.registro_casos(_, P.finalizar(P.codificar_parcial(v)), P.codificar_parcial(A.anexar_registro(S.campos(t), D.VRegistroVazio{}))) == P.Registro{S.quantidade_campos(xs), S.bytes_campos(xs)} : P.Parcial}
          %Equal.sym(Maybe<&2, List<&2, U32>>, P.finalizar(P.codificar_parcial(v)), Some{vb}, bytes) :
            {P.registro_casos(Some{nb}, _, P.codificar_parcial(A.anexar_registro(S.campos(t), D.VRegistroVazio{}))) == P.Registro{S.quantidade_campos(xs), S.bytes_campos(xs)} : P.Parcial}
          %Equal.sym(P.Parcial, P.codificar_parcial(A.anexar_registro(S.campos(t), D.VRegistroVazio{})), P.Registro{S.quantidade_campos(t), S.bytes_campos(t)}, resto_bytes) :
            {P.registro_casos(Some{nb}, Some{vb}, _) == P.Registro{S.quantidade_campos(xs), S.bytes_campos(xs)} : P.Parcial}
          Equal.cong(List<&2, U32>, P.Parcial, bs => P.Registro{1n+S.quantidade_campos(t), bs},
            B.concatenar(nb, B.concatenar(vb, S.bytes_campos(t))), B.concatenar(B.concatenar(nb, vb), S.bytes_campos(t)),
            Equal.sym(List<&2, U32>, B.concatenar(B.concatenar(nb, vb), S.bytes_campos(t)), B.concatenar(nb, B.concatenar(vb, S.bytes_campos(t))),
              K.concatenacao_associativa(nb, vb, S.bytes_campos(t)))))}}

law registro_segmentado_preserva_ordem_validade_e_parcial:
  for +xs: List<&2, S.CampoSegmentado>
  for +anterior: String
  for canonicos: S.CamposCanonicos(xs)
  for ordenados: A.CamposOrdenados(S.campos(xs), anterior)
  RegistroMontado(xs, anterior)
def registro_segmentado_preserva_ordem_validade_e_parcial(xs, anterior, canonicos, ordenados):
  match xs:
    case Nil{}:
      L.Ambos{{==}, L.Ambos{{==}, {==}}}
    case Con{S.CampoSegmentado{+n, +v, +nb, +vb}, +t}:
      match canonicos ordenados:
        case L.Ambos{nome, L.Ambos{nome_bytes, L.Ambos{valor, cauda}}} L.Ambos{nome2, L.Ambos{ordem, ordem_cauda}}:
          juntar_cabeca_registro(n, v, nb, vb, t, anterior, nome, ordem, nome_bytes,
            filho_canonico_expoe_validade_e_bytes(v, vb, valor),
            registro_segmentado_preserva_ordem_validade_e_parcial(t, n, cauda, ordem_cauda))

law campo_variavel_medido_tem_prefixo_exato:
  for +tag: U32
  for +n: Nat
  for +q: B.Numero64
  for +bs: List<&2, U32>
  for medida: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  {P.campo_variavel(tag, n, bs) == Some{prefixo(tag, q, bs)} : Maybe<&2, List<&2, U32>>}
def campo_variavel_medido_tem_prefixo_exato(tag, n, q, bs, medida):
  match q:
    case B.Numero64{+alto, +baixo}:
      %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{B.Numero64{alto, baixo}}, medida) :
        {P.prefixar_tamanho(tag, B.numero64_bytes(_), bs) == Some{prefixo(tag, B.Numero64{alto, baixo}, bs)} : Maybe<&2, List<&2, U32>>}
      {==}

def finalizar_lista_segmentada(+xs: List<&2, S.ValorSegmentado>, +q: B.Numero64,
  medida: {B.nat64(S.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>},
  montado: L.E<{D.valor_valido(A.anexar_lista(S.valores(xs), D.VListaVazia{})) == True{} : Bool}, {P.codificar_parcial(A.anexar_lista(S.valores(xs), D.VListaVazia{})) == P.Lista{S.quantidade_valores(xs), S.bytes_valores(xs)} : P.Parcial}>) -> P.Codificacao(A.anexar_lista(S.valores(xs), D.VListaVazia{}), prefixo(5, q, S.bytes_valores(xs))):
  match montado:
    case L.Ambos{valida, parcial}:
      Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(A.anexar_lista(S.valores(xs), D.VListaVazia{})),
        P.finalizar(P.codificar_parcial(A.anexar_lista(S.valores(xs), D.VListaVazia{}))), Some{prefixo(5, q, S.bytes_valores(xs))},
        K.valor_valido_libera_codificacao(A.anexar_lista(S.valores(xs), D.VListaVazia{}), valida),
        (%Equal.sym(P.Parcial, P.codificar_parcial(A.anexar_lista(S.valores(xs), D.VListaVazia{})), P.Lista{S.quantidade_valores(xs), S.bytes_valores(xs)}, parcial) :
          {P.finalizar(_) == Some{prefixo(5, q, S.bytes_valores(xs))} : Maybe<&2, List<&2, U32>>}
          campo_variavel_medido_tem_prefixo_exato(5, S.quantidade_valores(xs), q, S.bytes_valores(xs), medida)))

law lista_segmentada_tem_codificacao_canonica:
  for +xs: List<&2, S.ValorSegmentado>
  for +q: B.Numero64
  for canonicos: S.ValoresCanonicos(xs)
  for medida: {B.nat64(S.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  P.Codificacao(A.anexar_lista(S.valores(xs), D.VListaVazia{}), prefixo(5, q, S.bytes_valores(xs)))
def lista_segmentada_tem_codificacao_canonica(xs, q, canonicos, medida):
  finalizar_lista_segmentada(xs, q, medida, lista_segmentada_preserva_validade_e_parcial(xs, canonicos))

def finalizar_registro_segmentado(+xs: List<&2, S.CampoSegmentado>, +q: B.Numero64,
  medida: {B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
  montado: RegistroMontado(xs, "")) -> P.Codificacao(A.anexar_registro(S.campos(xs), D.VRegistroVazio{}), prefixo(6, q, S.bytes_campos(xs))):
  match montado:
    case L.Ambos{fronteira, L.Ambos{valida, parcial}}:
      Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(A.anexar_registro(S.campos(xs), D.VRegistroVazio{})),
        P.finalizar(P.codificar_parcial(A.anexar_registro(S.campos(xs), D.VRegistroVazio{}))), Some{prefixo(6, q, S.bytes_campos(xs))},
        K.valor_valido_libera_codificacao(A.anexar_registro(S.campos(xs), D.VRegistroVazio{}), valida),
        (%Equal.sym(P.Parcial, P.codificar_parcial(A.anexar_registro(S.campos(xs), D.VRegistroVazio{})), P.Registro{S.quantidade_campos(xs), S.bytes_campos(xs)}, parcial) :
          {P.finalizar(_) == Some{prefixo(6, q, S.bytes_campos(xs))} : Maybe<&2, List<&2, U32>>}
          campo_variavel_medido_tem_prefixo_exato(6, S.quantidade_campos(xs), q, S.bytes_campos(xs), medida)))

law registro_segmentado_tem_codificacao_canonica:
  for +xs: List<&2, S.CampoSegmentado>
  for +q: B.Numero64
  for canonicos: S.CamposCanonicos(xs)
  for ordenados: A.CamposOrdenados(S.campos(xs), "")
  for medida: {B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  P.Codificacao(A.anexar_registro(S.campos(xs), D.VRegistroVazio{}), prefixo(6, q, S.bytes_campos(xs)))
def registro_segmentado_tem_codificacao_canonica(xs, q, canonicos, ordenados, medida):
  finalizar_registro_segmentado(xs, q, medida, registro_segmentado_preserva_ordem_validade_e_parcial(xs, "", canonicos, ordenados))

# Cada nome preserva tag4, medida u64 e os bytes UTF-8 originais.
law nome_medido_tem_codificacao_textual_exata:
  for +nome: String
  for +utf8: List<&2, U32>
  for +q: B.Numero64
  for valido: {B.texto_valido(nome) == True{} : Bool}
  for bytes: {B.utf8(nome) == utf8 : List<&2, U32>}
  for medida: {B.nat64(B.comprimento(utf8)) == Some{q} : Maybe<&2, B.Numero64>}
  {P.texto(nome) == Some{prefixo(4, q, utf8)} : Maybe<&2, List<&2, U32>>}
def nome_medido_tem_codificacao_textual_exata(nome, utf8, q, valido, bytes, medida):
  %Equal.sym(Bool, B.texto_valido(nome), True{}, valido) :
    {P.texto_casos(_, B.utf8(nome)) == Some{prefixo(4, q, utf8)} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, B.utf8(nome), utf8, bytes) :
    {P.campo_variavel(4, B.comprimento(_), _) == Some{prefixo(4, q, utf8)} : Maybe<&2, List<&2, U32>>}
  campo_variavel_medido_tem_prefixo_exato(4, B.comprimento(utf8), q, utf8, medida)
