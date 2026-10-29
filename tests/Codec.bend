import Base
import ../src/Codec.bend as C
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P

# Exemplos fechados sao provas por avaliacao, rechecadas por --verdict.
# O encoder de referencia de contrato/ conserva sua definicao canonica.
def limite() -> B.Numero64:
  B.Numero64{4294967295, 4294967295}

def ler(bs: List<&2, U32>) -> C.Resultado:
  C.decodificar(bs, limite())

def texto_bruto(+bs: List<&2, U32>) -> List<&2, U32>:
  Con{4, B.concatenar(B.be64(0, U32.from_nat(B.comprimento(bs))), bs)}

def referencia_codificada(bs: Maybe<&2, List<&2, U32>>) -> C.Resultado:
  match bs:
    case None{}:
      C.Entrada{}
    case Some{xs}:
      ler(xs)

def referencia(v: D.Valor) -> C.Resultado:
  referencia_codificada(P.codificar(v))

def amostra() -> D.Valor:
  D.VRegistro{"A", D.VLista{D.VAusente{}, D.VLista{D.VBool{False{}}, D.VLista{D.VBool{True{}}, D.VLista{D.VInt{2147483648, 0}, D.VListaVazia{}}}}},
    D.VRegistro{"_", D.VRegistroVazio{},
      D.VRegistro{"a0", D.VTexto{"Aç𝄞"},
        D.VRegistro{"z", D.VLista{D.VListaVazia{}, D.VLista{D.VRegistro{"x", D.VTexto{""}, D.VRegistroVazio{}}, D.VListaVazia{}}}, D.VRegistroVazio{}}}}}

law todos_os_tipos_em_estrutura_geral:
  {referencia(amostra()) == C.Decodificado{amostra()} : C.Resultado}
def todos_os_tipos_em_estrutura_geral():
  {==}

law tags_atomicas:
  {(ler([0]), (ler([1]), ler([2]))) ==
   (C.Decodificado{D.VAusente{}}, (C.Decodificado{D.VBool{False{}}}, C.Decodificado{D.VBool{True{}}})) : C.Resultado & (C.Resultado & C.Resultado)}
def tags_atomicas():
  {==}

law inteiros_extremos_e_words:
  {(ler([3, 128, 0, 0, 0, 0, 0, 0, 0]),
    (ler([3, 127, 255, 255, 255, 255, 255, 255, 255]),
      ler([3, 255, 255, 255, 255, 255, 255, 255, 255]))) ==
   (C.Decodificado{D.VInt{2147483648, 0}},
    (C.Decodificado{D.VInt{2147483647, 4294967295}}, C.Decodificado{D.VInt{4294967295, 4294967295}})) : C.Resultado & (C.Resultado & C.Resultado)}
def inteiros_extremos_e_words():
  {==}

law inteiro_big_endian_sem_conversao:
  {ler([3, 1, 35, 69, 103, 137, 171, 205, 239]) == C.Decodificado{D.VInt{19088743, 2309737967}} : C.Resultado}
def inteiro_big_endian_sem_conversao():
  {==}

law inteiro_zero:
  {ler([3, 0, 0, 0, 0, 0, 0, 0, 0]) == C.Decodificado{D.VInt{0, 0}} : C.Resultado}
def inteiro_zero():
  {==}

law vazios:
  {(ler([4, 0, 0, 0, 0, 0, 0, 0, 0]),
    (ler([5, 0, 0, 0, 0, 0, 0, 0, 0]), ler([6, 0, 0, 0, 0, 0, 0, 0, 0]))) ==
   (C.Decodificado{D.VTexto{""}}, (C.Decodificado{D.VListaVazia{}}, C.Decodificado{D.VRegistroVazio{}})) : C.Resultado & (C.Resultado & C.Resultado)}
def vazios():
  {==}

law lista_heterogenea_bytes_originais:
  {ler([5, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 2]) ==
    C.Decodificado{D.VLista{D.VAusente{}, D.VLista{D.VBool{False{}}, D.VLista{D.VBool{True{}}, D.VListaVazia{}}}}} : C.Resultado}
def lista_heterogenea_bytes_originais():
  {==}

law utf8_limites_escalares:
  {ler(texto_bruto([0, 127, 194, 128, 223, 191, 224, 160, 128, 237, 159, 191, 238, 128, 128, 239, 191, 191, 240, 144, 128, 128, 244, 143, 191, 191])) ==
    C.Decodificado{D.VTexto{SCon{Chr{0}, SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{55295}, SCon{Chr{57344}, SCon{Chr{65535}, SCon{Chr{65536}, SCon{Chr{1114111}, SNil{}}}}}}}}}}}}} : C.Resultado}
def utf8_limites_escalares():
  {==}

law unicode_preservado_sem_normalizacao:
  {referencia(D.VLista{D.VTexto{"é"}, D.VLista{D.VTexto{"é"}, D.VListaVazia{}}}) ==
    C.Decodificado{D.VLista{D.VTexto{"é"}, D.VLista{D.VTexto{"é"}, D.VListaVazia{}}}} : C.Resultado}
def unicode_preservado_sem_normalizacao():
  {==}

law caractere_substituicao_explicito_e_valido:
  {ler(texto_bruto([239, 191, 189])) == C.Decodificado{D.VTexto{"�"}} : C.Resultado}
def caractere_substituicao_explicito_e_valido():
  {==}

def e_entrada(r: C.Resultado) -> Bool:
  match r:
    case C.Entrada{}:
      True{}
    case _:
      False{}

def e_limite(r: C.Resultado) -> Bool:
  match r:
    case C.Limite{}:
      True{}
    case _:
      False{}

def textos_invalidos(xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      e_entrada(ler(texto_bruto(h))) && textos_invalidos(t)

law utf8_estrito_sem_substituicao:
  {textos_invalidos([[128], [191], [192, 128], [193, 191],
    [194], [194, 0], [194, 192], [223, 255],
    [224, 128, 128], [224, 159, 191], [225, 128], [225, 65, 128],
    [237, 160, 128], [237, 191, 191],
    [240, 128, 128, 128], [240, 143, 191, 191], [240, 159, 146],
    [241, 128, 128, 0], [244, 144, 128, 128], [245, 128, 128, 128],
    [248], [252], [254], [255], [65, 128], [239, 191]]) == True{} : Bool}
def utf8_estrito_sem_substituicao():
  {==}

def registro_um_nome(nome: String) -> C.Resultado:
  referencia_codificada(P.concatenar_opcional(Some{Con{6, B.be64(0, 1)}}, P.concatenar_opcional(P.texto(nome), Some{[0]})))

law nomes_invalidos:
  {(e_entrada(registro_um_nome("")) && e_entrada(registro_um_nome("0x")) &&
    e_entrada(registro_um_nome("a-b")) && e_entrada(registro_um_nome("a b")) &&
    e_entrada(registro_um_nome("á")) && e_entrada(registro_um_nome("a\n")) &&
    e_entrada(registro_um_nome("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"))) == True{} : Bool}
def nomes_invalidos():
  {==}

law nome_de_64_ascii:
  {registro_um_nome("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") ==
    C.Decodificado{D.VRegistro{"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", D.VAusente{}, D.VRegistroVazio{}}} : C.Resultado}
def nome_de_64_ascii():
  {==}

law nomes_ascii_e_ordem_case_sensitive:
  {referencia(D.VRegistro{"A_09", D.VAusente{}, D.VRegistro{"Z", D.VAusente{}, D.VRegistro{"_", D.VAusente{}, D.VRegistro{"a", D.VAusente{}, D.VRegistroVazio{}}}}}) ==
    C.Decodificado{D.VRegistro{"A_09", D.VAusente{}, D.VRegistro{"Z", D.VAusente{}, D.VRegistro{"_", D.VAusente{}, D.VRegistro{"a", D.VAusente{}, D.VRegistroVazio{}}}}}} : C.Resultado}
def nomes_ascii_e_ordem_case_sensitive():
  {==}

def campo_bruto(n: String, v: List<&2, U32>) -> List<&2, U32>:
  B.concatenar(texto_bruto(B.utf8(n)), v)

def registro_dois(a: String, b: String) -> C.Resultado:
  ler(B.concatenar(Con{6, B.be64(0, 2)}, B.concatenar(campo_bruto(a, [0]), campo_bruto(b, [2]))))

law registros_duplicados_desordenados:
  {(e_entrada(registro_dois("a", "a")) && e_entrada(registro_dois("b", "a")) &&
    e_entrada(registro_dois("a", "A")) && e_entrada(registro_dois("aa", "a"))) == True{} : Bool}
def registros_duplicados_desordenados():
  {==}

law ordem_de_prefixos:
  {registro_dois("a", "aa") == C.Decodificado{D.VRegistro{"a", D.VAusente{}, D.VRegistro{"aa", D.VBool{True{}}, D.VRegistroVazio{}}}} : C.Resultado}
def ordem_de_prefixos():
  {==}

law nome_exige_tag_de_texto:
  {ler([6, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) == C.Entrada{} : C.Resultado}
def nome_exige_tag_de_texto():
  {==}

law ordem_local_independente_do_ancestral:
  {referencia(D.VRegistro{"z", D.VRegistro{"a", D.VAusente{}, D.VRegistroVazio{}}, D.VRegistroVazio{}}) ==
    C.Decodificado{D.VRegistro{"z", D.VRegistro{"a", D.VAusente{}, D.VRegistroVazio{}}, D.VRegistroVazio{}}} : C.Resultado}
def ordem_local_independente_do_ancestral():
  {==}

def entradas_invalidas(xs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      e_entrada(ler(h)) && entradas_invalidas(t)

law malformados_e_bytes_extras:
  {entradas_invalidas([[], [7], [255], [256], [4294967295], [0, 0], [1, 2],
    [3], [3, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [4, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0, 0, 2, 65],
    [4, 0, 0, 0, 0, 0, 0, 0, 1, 65, 66],
    [5, 0, 0, 0, 0, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0, 0, 1],
    [5, 0, 0, 0, 0, 0, 0, 0, 2, 0], [5, 0, 0, 0, 0, 0, 0, 0, 1, 7],
    [6, 0, 0, 0, 0, 0, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0, 0, 1],
    [5, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1, 256]]) == True{} : Bool}
def malformados_e_bytes_extras():
  {==}

law limite_inclusivo:
  {(C.decodificar([0], B.Numero64{0, 1}),
    (C.decodificar([0], B.Numero64{0, 0}), C.decodificar([], B.Numero64{0, 0}))) ==
   (C.Decodificado{D.VAusente{}}, (C.Limite{}, C.Entrada{})) : C.Resultado & (C.Resultado & C.Resultado)}
def limite_inclusivo():
  {==}

law tamanho_do_corpo_precede_decodificacao:
  {C.decodificar([255, 255], B.Numero64{0, 1}) == C.Limite{} : C.Resultado}
def tamanho_do_corpo_precede_decodificacao():
  {==}

law comprimento_truncado_vs_acima_do_limite:
  {(C.decodificar([4, 0, 0, 0, 0, 0, 0, 0, 2], B.Numero64{0, 11}),
    C.decodificar([4, 0, 0, 0, 0, 0, 0, 0, 2], B.Numero64{0, 10})) ==
   (C.Entrada{}, C.Limite{}) : C.Resultado & C.Resultado}
def comprimento_truncado_vs_acima_do_limite():
  {==}

law texto_no_limite_exato:
  {C.decodificar([4, 0, 0, 0, 0, 0, 0, 0, 2, 194, 128], B.Numero64{0, 11}) == C.Decodificado{D.VTexto{SCon{Chr{128}, SNil{}}}} : C.Resultado}
def texto_no_limite_exato():
  {==}

law contador_u64_nao_trunca_para_u32:
  {(C.decodificar([5, 0, 0, 0, 1, 0, 0, 0, 0], B.Numero64{0, 100}),
    ler([5, 0, 0, 0, 1, 0, 0, 0, 0])) == (C.Limite{}, C.Entrada{}) : C.Resultado & C.Resultado}
def contador_u64_nao_trunca_para_u32():
  {==}

law comprimento_u64_nao_trunca_para_u32:
  {(C.decodificar([4, 0, 0, 0, 1, 0, 0, 0, 0], B.Numero64{0, 100}),
    ler([4, 0, 0, 0, 1, 0, 0, 0, 0])) == (C.Limite{}, C.Entrada{}) : C.Resultado & C.Resultado}
def comprimento_u64_nao_trunca_para_u32():
  {==}

law maximo_u64_mais_cabecalho_nao_cabe:
  {(e_limite(ler([4, 255, 255, 255, 255, 255, 255, 255, 255])) &&
    e_limite(ler([5, 255, 255, 255, 255, 255, 255, 255, 255])) &&
    e_limite(ler([6, 255, 255, 255, 255, 255, 255, 255, 255]))) == True{} : Bool}
def maximo_u64_mais_cabecalho_nao_cabe():
  {==}

law minimo_de_registro_detecta_overflow_u64:
  {ler([6, 32, 0, 0, 0, 0, 0, 0, 0]) == C.Limite{} : C.Resultado}
def minimo_de_registro_detecta_overflow_u64():
  {==}

law quantidade_de_registro_verificada_antes_dos_pares:
  {(C.decodificar([6, 0, 0, 0, 0, 0, 0, 0, 1], B.Numero64{0, 19}),
    C.decodificar([6, 0, 0, 0, 0, 0, 0, 0, 1], B.Numero64{0, 20})) ==
   (C.Limite{}, C.Entrada{}) : C.Resultado & C.Resultado}
def quantidade_de_registro_verificada_antes_dos_pares():
  {==}

law limite_inclui_irmaos_pendentes:
  {C.decodificar([5, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 3], B.Numero64{0, 21}) == C.Limite{} : C.Resultado}
def limite_inclui_irmaos_pendentes():
  {==}

law limite_inclui_valor_depois_do_nome:
  {C.decodificar([6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 3, 97, 98], B.Numero64{0, 21}) == C.Limite{} : C.Resultado}
def limite_inclui_valor_depois_do_nome():
  {==}

# Cada igualdade verifica um prefixo; a divisao evita o teto de avaliacao
# de uma unica igualdade no kernel, sem limitar o parser ou os casos.
def prefixos_trecho(n: Nat, +bs: List<&2, U32>, +pos: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      e_entrada(ler(List.take(&2, U32, bs, pos))) && prefixos_trecho(p, bs, 1n+pos)

def prefixos_codificados(m: Maybe<&2, List<&2, U32>>, n: Nat, pos: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{bs}:
      prefixos_trecho(n, bs, pos)

def prefixos_amostra(n: Nat, pos: Nat) -> Bool:
  prefixos_codificados(P.codificar(amostra()), n, pos)

def tamanho_codificado(m: Maybe<&2, List<&2, U32>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{bs}:
      B.comprimento(bs)

law tamanho_da_amostra:
  {tamanho_codificado(P.codificar(amostra())) == 142n : Nat}
def tamanho_da_amostra():
  {==}

law prefixo_0:
  {prefixos_amostra(1n, 0n) == True{} : Bool}
def prefixo_0():
  {==}

law prefixo_1:
  {prefixos_amostra(1n, 1n) == True{} : Bool}
def prefixo_1():
  {==}

law prefixo_2:
  {prefixos_amostra(1n, 2n) == True{} : Bool}
def prefixo_2():
  {==}

law prefixo_3:
  {prefixos_amostra(1n, 3n) == True{} : Bool}
def prefixo_3():
  {==}

law prefixo_4:
  {prefixos_amostra(1n, 4n) == True{} : Bool}
def prefixo_4():
  {==}

law prefixo_5:
  {prefixos_amostra(1n, 5n) == True{} : Bool}
def prefixo_5():
  {==}

law prefixo_6:
  {prefixos_amostra(1n, 6n) == True{} : Bool}
def prefixo_6():
  {==}

law prefixo_7:
  {prefixos_amostra(1n, 7n) == True{} : Bool}
def prefixo_7():
  {==}

law prefixo_8:
  {prefixos_amostra(1n, 8n) == True{} : Bool}
def prefixo_8():
  {==}

law prefixo_9:
  {prefixos_amostra(1n, 9n) == True{} : Bool}
def prefixo_9():
  {==}

law prefixo_10:
  {prefixos_amostra(1n, 10n) == True{} : Bool}
def prefixo_10():
  {==}

law prefixo_11:
  {prefixos_amostra(1n, 11n) == True{} : Bool}
def prefixo_11():
  {==}

law prefixo_12:
  {prefixos_amostra(1n, 12n) == True{} : Bool}
def prefixo_12():
  {==}

law prefixo_13:
  {prefixos_amostra(1n, 13n) == True{} : Bool}
def prefixo_13():
  {==}

law prefixo_14:
  {prefixos_amostra(1n, 14n) == True{} : Bool}
def prefixo_14():
  {==}

law prefixo_15:
  {prefixos_amostra(1n, 15n) == True{} : Bool}
def prefixo_15():
  {==}

law prefixo_16:
  {prefixos_amostra(1n, 16n) == True{} : Bool}
def prefixo_16():
  {==}

law prefixo_17:
  {prefixos_amostra(1n, 17n) == True{} : Bool}
def prefixo_17():
  {==}

law prefixo_18:
  {prefixos_amostra(1n, 18n) == True{} : Bool}
def prefixo_18():
  {==}

law prefixo_19:
  {prefixos_amostra(1n, 19n) == True{} : Bool}
def prefixo_19():
  {==}

law prefixo_20:
  {prefixos_amostra(1n, 20n) == True{} : Bool}
def prefixo_20():
  {==}

law prefixo_21:
  {prefixos_amostra(1n, 21n) == True{} : Bool}
def prefixo_21():
  {==}

law prefixo_22:
  {prefixos_amostra(1n, 22n) == True{} : Bool}
def prefixo_22():
  {==}

law prefixo_23:
  {prefixos_amostra(1n, 23n) == True{} : Bool}
def prefixo_23():
  {==}

law prefixo_24:
  {prefixos_amostra(1n, 24n) == True{} : Bool}
def prefixo_24():
  {==}

law prefixo_25:
  {prefixos_amostra(1n, 25n) == True{} : Bool}
def prefixo_25():
  {==}

law prefixo_26:
  {prefixos_amostra(1n, 26n) == True{} : Bool}
def prefixo_26():
  {==}

law prefixo_27:
  {prefixos_amostra(1n, 27n) == True{} : Bool}
def prefixo_27():
  {==}

law prefixo_28:
  {prefixos_amostra(1n, 28n) == True{} : Bool}
def prefixo_28():
  {==}

law prefixo_29:
  {prefixos_amostra(1n, 29n) == True{} : Bool}
def prefixo_29():
  {==}

law prefixo_30:
  {prefixos_amostra(1n, 30n) == True{} : Bool}
def prefixo_30():
  {==}

law prefixo_31:
  {prefixos_amostra(1n, 31n) == True{} : Bool}
def prefixo_31():
  {==}

law prefixo_32:
  {prefixos_amostra(1n, 32n) == True{} : Bool}
def prefixo_32():
  {==}

law prefixo_33:
  {prefixos_amostra(1n, 33n) == True{} : Bool}
def prefixo_33():
  {==}

law prefixo_34:
  {prefixos_amostra(1n, 34n) == True{} : Bool}
def prefixo_34():
  {==}

law prefixo_35:
  {prefixos_amostra(1n, 35n) == True{} : Bool}
def prefixo_35():
  {==}

law prefixo_36:
  {prefixos_amostra(1n, 36n) == True{} : Bool}
def prefixo_36():
  {==}

law prefixo_37:
  {prefixos_amostra(1n, 37n) == True{} : Bool}
def prefixo_37():
  {==}

law prefixo_38:
  {prefixos_amostra(1n, 38n) == True{} : Bool}
def prefixo_38():
  {==}

law prefixo_39:
  {prefixos_amostra(1n, 39n) == True{} : Bool}
def prefixo_39():
  {==}

law prefixo_40:
  {prefixos_amostra(1n, 40n) == True{} : Bool}
def prefixo_40():
  {==}

law prefixo_41:
  {prefixos_amostra(1n, 41n) == True{} : Bool}
def prefixo_41():
  {==}

law prefixo_42:
  {prefixos_amostra(1n, 42n) == True{} : Bool}
def prefixo_42():
  {==}

law prefixo_43:
  {prefixos_amostra(1n, 43n) == True{} : Bool}
def prefixo_43():
  {==}

law prefixo_44:
  {prefixos_amostra(1n, 44n) == True{} : Bool}
def prefixo_44():
  {==}

law prefixo_45:
  {prefixos_amostra(1n, 45n) == True{} : Bool}
def prefixo_45():
  {==}

law prefixo_46:
  {prefixos_amostra(1n, 46n) == True{} : Bool}
def prefixo_46():
  {==}

law prefixo_47:
  {prefixos_amostra(1n, 47n) == True{} : Bool}
def prefixo_47():
  {==}

law prefixo_48:
  {prefixos_amostra(1n, 48n) == True{} : Bool}
def prefixo_48():
  {==}

law prefixo_49:
  {prefixos_amostra(1n, 49n) == True{} : Bool}
def prefixo_49():
  {==}

law prefixo_50:
  {prefixos_amostra(1n, 50n) == True{} : Bool}
def prefixo_50():
  {==}

law prefixo_51:
  {prefixos_amostra(1n, 51n) == True{} : Bool}
def prefixo_51():
  {==}

law prefixo_52:
  {prefixos_amostra(1n, 52n) == True{} : Bool}
def prefixo_52():
  {==}

law prefixo_53:
  {prefixos_amostra(1n, 53n) == True{} : Bool}
def prefixo_53():
  {==}

law prefixo_54:
  {prefixos_amostra(1n, 54n) == True{} : Bool}
def prefixo_54():
  {==}

law prefixo_55:
  {prefixos_amostra(1n, 55n) == True{} : Bool}
def prefixo_55():
  {==}

law prefixo_56:
  {prefixos_amostra(1n, 56n) == True{} : Bool}
def prefixo_56():
  {==}

law prefixo_57:
  {prefixos_amostra(1n, 57n) == True{} : Bool}
def prefixo_57():
  {==}

law prefixo_58:
  {prefixos_amostra(1n, 58n) == True{} : Bool}
def prefixo_58():
  {==}

law prefixo_59:
  {prefixos_amostra(1n, 59n) == True{} : Bool}
def prefixo_59():
  {==}

law prefixo_60:
  {prefixos_amostra(1n, 60n) == True{} : Bool}
def prefixo_60():
  {==}

law prefixo_61:
  {prefixos_amostra(1n, 61n) == True{} : Bool}
def prefixo_61():
  {==}

law prefixo_62:
  {prefixos_amostra(1n, 62n) == True{} : Bool}
def prefixo_62():
  {==}

law prefixo_63:
  {prefixos_amostra(1n, 63n) == True{} : Bool}
def prefixo_63():
  {==}

law prefixo_64:
  {prefixos_amostra(1n, 64n) == True{} : Bool}
def prefixo_64():
  {==}

law prefixo_65:
  {prefixos_amostra(1n, 65n) == True{} : Bool}
def prefixo_65():
  {==}

law prefixo_66:
  {prefixos_amostra(1n, 66n) == True{} : Bool}
def prefixo_66():
  {==}

law prefixo_67:
  {prefixos_amostra(1n, 67n) == True{} : Bool}
def prefixo_67():
  {==}

law prefixo_68:
  {prefixos_amostra(1n, 68n) == True{} : Bool}
def prefixo_68():
  {==}

law prefixo_69:
  {prefixos_amostra(1n, 69n) == True{} : Bool}
def prefixo_69():
  {==}

law prefixo_70:
  {prefixos_amostra(1n, 70n) == True{} : Bool}
def prefixo_70():
  {==}

law prefixo_71:
  {prefixos_amostra(1n, 71n) == True{} : Bool}
def prefixo_71():
  {==}

law prefixo_72:
  {prefixos_amostra(1n, 72n) == True{} : Bool}
def prefixo_72():
  {==}

law prefixo_73:
  {prefixos_amostra(1n, 73n) == True{} : Bool}
def prefixo_73():
  {==}

law prefixo_74:
  {prefixos_amostra(1n, 74n) == True{} : Bool}
def prefixo_74():
  {==}

law prefixo_75:
  {prefixos_amostra(1n, 75n) == True{} : Bool}
def prefixo_75():
  {==}

law prefixo_76:
  {prefixos_amostra(1n, 76n) == True{} : Bool}
def prefixo_76():
  {==}

law prefixo_77:
  {prefixos_amostra(1n, 77n) == True{} : Bool}
def prefixo_77():
  {==}

law prefixo_78:
  {prefixos_amostra(1n, 78n) == True{} : Bool}
def prefixo_78():
  {==}

law prefixo_79:
  {prefixos_amostra(1n, 79n) == True{} : Bool}
def prefixo_79():
  {==}

law prefixo_80:
  {prefixos_amostra(1n, 80n) == True{} : Bool}
def prefixo_80():
  {==}

law prefixo_81:
  {prefixos_amostra(1n, 81n) == True{} : Bool}
def prefixo_81():
  {==}

law prefixo_82:
  {prefixos_amostra(1n, 82n) == True{} : Bool}
def prefixo_82():
  {==}

law prefixo_83:
  {prefixos_amostra(1n, 83n) == True{} : Bool}
def prefixo_83():
  {==}

law prefixo_84:
  {prefixos_amostra(1n, 84n) == True{} : Bool}
def prefixo_84():
  {==}

law prefixo_85:
  {prefixos_amostra(1n, 85n) == True{} : Bool}
def prefixo_85():
  {==}

law prefixo_86:
  {prefixos_amostra(1n, 86n) == True{} : Bool}
def prefixo_86():
  {==}

law prefixo_87:
  {prefixos_amostra(1n, 87n) == True{} : Bool}
def prefixo_87():
  {==}

law prefixo_88:
  {prefixos_amostra(1n, 88n) == True{} : Bool}
def prefixo_88():
  {==}

law prefixo_89:
  {prefixos_amostra(1n, 89n) == True{} : Bool}
def prefixo_89():
  {==}

law prefixo_90:
  {prefixos_amostra(1n, 90n) == True{} : Bool}
def prefixo_90():
  {==}

law prefixo_91:
  {prefixos_amostra(1n, 91n) == True{} : Bool}
def prefixo_91():
  {==}

law prefixo_92:
  {prefixos_amostra(1n, 92n) == True{} : Bool}
def prefixo_92():
  {==}

law prefixo_93:
  {prefixos_amostra(1n, 93n) == True{} : Bool}
def prefixo_93():
  {==}

law prefixo_94:
  {prefixos_amostra(1n, 94n) == True{} : Bool}
def prefixo_94():
  {==}

law prefixo_95:
  {prefixos_amostra(1n, 95n) == True{} : Bool}
def prefixo_95():
  {==}

law prefixo_96:
  {prefixos_amostra(1n, 96n) == True{} : Bool}
def prefixo_96():
  {==}

law prefixo_97:
  {prefixos_amostra(1n, 97n) == True{} : Bool}
def prefixo_97():
  {==}

law prefixo_98:
  {prefixos_amostra(1n, 98n) == True{} : Bool}
def prefixo_98():
  {==}

law prefixo_99:
  {prefixos_amostra(1n, 99n) == True{} : Bool}
def prefixo_99():
  {==}

law prefixo_100:
  {prefixos_amostra(1n, 100n) == True{} : Bool}
def prefixo_100():
  {==}

law prefixo_101:
  {prefixos_amostra(1n, 101n) == True{} : Bool}
def prefixo_101():
  {==}

law prefixo_102:
  {prefixos_amostra(1n, 102n) == True{} : Bool}
def prefixo_102():
  {==}

law prefixo_103:
  {prefixos_amostra(1n, 103n) == True{} : Bool}
def prefixo_103():
  {==}

law prefixo_104:
  {prefixos_amostra(1n, 104n) == True{} : Bool}
def prefixo_104():
  {==}

law prefixo_105:
  {prefixos_amostra(1n, 105n) == True{} : Bool}
def prefixo_105():
  {==}

law prefixo_106:
  {prefixos_amostra(1n, 106n) == True{} : Bool}
def prefixo_106():
  {==}

law prefixo_107:
  {prefixos_amostra(1n, 107n) == True{} : Bool}
def prefixo_107():
  {==}

law prefixo_108:
  {prefixos_amostra(1n, 108n) == True{} : Bool}
def prefixo_108():
  {==}

law prefixo_109:
  {prefixos_amostra(1n, 109n) == True{} : Bool}
def prefixo_109():
  {==}

law prefixo_110:
  {prefixos_amostra(1n, 110n) == True{} : Bool}
def prefixo_110():
  {==}

law prefixo_111:
  {prefixos_amostra(1n, 111n) == True{} : Bool}
def prefixo_111():
  {==}

law prefixo_112:
  {prefixos_amostra(1n, 112n) == True{} : Bool}
def prefixo_112():
  {==}

law prefixo_113:
  {prefixos_amostra(1n, 113n) == True{} : Bool}
def prefixo_113():
  {==}

law prefixo_114:
  {prefixos_amostra(1n, 114n) == True{} : Bool}
def prefixo_114():
  {==}

law prefixo_115:
  {prefixos_amostra(1n, 115n) == True{} : Bool}
def prefixo_115():
  {==}

law prefixo_116:
  {prefixos_amostra(1n, 116n) == True{} : Bool}
def prefixo_116():
  {==}

law prefixo_117:
  {prefixos_amostra(1n, 117n) == True{} : Bool}
def prefixo_117():
  {==}

law prefixo_118:
  {prefixos_amostra(1n, 118n) == True{} : Bool}
def prefixo_118():
  {==}

law prefixo_119:
  {prefixos_amostra(1n, 119n) == True{} : Bool}
def prefixo_119():
  {==}

law prefixo_120:
  {prefixos_amostra(1n, 120n) == True{} : Bool}
def prefixo_120():
  {==}

law prefixo_121:
  {prefixos_amostra(1n, 121n) == True{} : Bool}
def prefixo_121():
  {==}

law prefixo_122:
  {prefixos_amostra(1n, 122n) == True{} : Bool}
def prefixo_122():
  {==}

law prefixo_123:
  {prefixos_amostra(1n, 123n) == True{} : Bool}
def prefixo_123():
  {==}

law prefixo_124:
  {prefixos_amostra(1n, 124n) == True{} : Bool}
def prefixo_124():
  {==}

law prefixo_125:
  {prefixos_amostra(1n, 125n) == True{} : Bool}
def prefixo_125():
  {==}

law prefixo_126:
  {prefixos_amostra(1n, 126n) == True{} : Bool}
def prefixo_126():
  {==}

law prefixo_127:
  {prefixos_amostra(1n, 127n) == True{} : Bool}
def prefixo_127():
  {==}

law prefixo_128:
  {prefixos_amostra(1n, 128n) == True{} : Bool}
def prefixo_128():
  {==}

law prefixo_129:
  {prefixos_amostra(1n, 129n) == True{} : Bool}
def prefixo_129():
  {==}

law prefixo_130:
  {prefixos_amostra(1n, 130n) == True{} : Bool}
def prefixo_130():
  {==}

law prefixo_131:
  {prefixos_amostra(1n, 131n) == True{} : Bool}
def prefixo_131():
  {==}

law prefixo_132:
  {prefixos_amostra(1n, 132n) == True{} : Bool}
def prefixo_132():
  {==}

law prefixo_133:
  {prefixos_amostra(1n, 133n) == True{} : Bool}
def prefixo_133():
  {==}

law prefixo_134:
  {prefixos_amostra(1n, 134n) == True{} : Bool}
def prefixo_134():
  {==}

law prefixo_135:
  {prefixos_amostra(1n, 135n) == True{} : Bool}
def prefixo_135():
  {==}

law prefixo_136:
  {prefixos_amostra(1n, 136n) == True{} : Bool}
def prefixo_136():
  {==}

law prefixo_137:
  {prefixos_amostra(1n, 137n) == True{} : Bool}
def prefixo_137():
  {==}

law prefixo_138:
  {prefixos_amostra(1n, 138n) == True{} : Bool}
def prefixo_138():
  {==}

law prefixo_139:
  {prefixos_amostra(1n, 139n) == True{} : Bool}
def prefixo_139():
  {==}

law prefixo_140:
  {prefixos_amostra(1n, 140n) == True{} : Bool}
def prefixo_140():
  {==}

law prefixo_141:
  {prefixos_amostra(1n, 141n) == True{} : Bool}
def prefixo_141():
  {==}

# Familia de valores gerais: profundidade e largura independentes.
def aninhar(n: Nat, v: D.Valor) -> D.Valor:
  match n:
    case 0n:
      v
    case 1n+p:
      aninhar(p, D.VRegistro{"x", D.VLista{v, D.VLista{D.VBool{True{}}, D.VListaVazia{}}}, D.VRegistroVazio{}})

# O caso de 64 niveis continua em main. Uma igualdade monolitica desse
# tamanho excede o combustivel de normalizacao de BendTT 2.0.39; o kernel
# verifica as definicoes deste teste, e bend tests/Codec.bend o executa.
law dezesseis_niveis_em_prova_fechada:
  {referencia(aninhar(8n, D.VAusente{})) == C.Decodificado{aninhar(8n, D.VAusente{})} : C.Resultado}
def dezesseis_niveis_em_prova_fechada():
  {==}

def bytes_iguais(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      U32.is_eq(x, y) && bytes_iguais(xs, ys)
    case _ _:
      False{}

def recodificado(m: Maybe<&2, List<&2, U32>>, bs: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      bytes_iguais(xs, bs)

def canonico(r: C.Resultado, bs: List<&2, U32>) -> Bool:
  match r:
    case C.Decodificado{v}:
      recodificado(P.codificar(v), bs)
    case _:
      True{}

def testar_bytes(+bs: List<&2, U32>) -> Bool:
  canonico(ler(bs), bs)

def variar_octeto(+n: Nat, +inicio: Nat, +antes: List<&2, U32>, +depois: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      testar_bytes(B.concatenar(antes, Con{U32.from_nat((inicio + p : Nat)), depois})) && variar_octeto(p, inicio, antes, depois)

# Os mesmos 768 casos, repartidos em provas com dezesseis casos cada.
law octetos_tags_0_15:
  {variar_octeto(16n, 0n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_0_15():
  {==}

law octetos_tags_16_31:
  {variar_octeto(16n, 16n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_16_31():
  {==}

law octetos_tags_32_47:
  {variar_octeto(16n, 32n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_32_47():
  {==}

law octetos_tags_48_63:
  {variar_octeto(16n, 48n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_48_63():
  {==}

law octetos_tags_64_79:
  {variar_octeto(16n, 64n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_64_79():
  {==}

law octetos_tags_80_95:
  {variar_octeto(16n, 80n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_80_95():
  {==}

law octetos_tags_96_111:
  {variar_octeto(16n, 96n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_96_111():
  {==}

law octetos_tags_112_127:
  {variar_octeto(16n, 112n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_112_127():
  {==}

law octetos_tags_128_143:
  {variar_octeto(16n, 128n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_128_143():
  {==}

law octetos_tags_144_159:
  {variar_octeto(16n, 144n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_144_159():
  {==}

law octetos_tags_160_175:
  {variar_octeto(16n, 160n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_160_175():
  {==}

law octetos_tags_176_191:
  {variar_octeto(16n, 176n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_176_191():
  {==}

law octetos_tags_192_207:
  {variar_octeto(16n, 192n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_192_207():
  {==}

law octetos_tags_208_223:
  {variar_octeto(16n, 208n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_208_223():
  {==}

law octetos_tags_224_239:
  {variar_octeto(16n, 224n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_224_239():
  {==}

law octetos_tags_240_255:
  {variar_octeto(16n, 240n, Nil{}, Nil{}) == True{} : Bool}
def octetos_tags_240_255():
  {==}

law octetos_textuais_0_15:
  {variar_octeto(16n, 0n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_0_15():
  {==}

law octetos_textuais_16_31:
  {variar_octeto(16n, 16n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_16_31():
  {==}

law octetos_textuais_32_47:
  {variar_octeto(16n, 32n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_32_47():
  {==}

law octetos_textuais_48_63:
  {variar_octeto(16n, 48n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_48_63():
  {==}

law octetos_textuais_64_79:
  {variar_octeto(16n, 64n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_64_79():
  {==}

law octetos_textuais_80_95:
  {variar_octeto(16n, 80n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_80_95():
  {==}

law octetos_textuais_96_111:
  {variar_octeto(16n, 96n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_96_111():
  {==}

law octetos_textuais_112_127:
  {variar_octeto(16n, 112n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_112_127():
  {==}

law octetos_textuais_128_143:
  {variar_octeto(16n, 128n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_128_143():
  {==}

law octetos_textuais_144_159:
  {variar_octeto(16n, 144n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_144_159():
  {==}

law octetos_textuais_160_175:
  {variar_octeto(16n, 160n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_160_175():
  {==}

law octetos_textuais_176_191:
  {variar_octeto(16n, 176n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_176_191():
  {==}

law octetos_textuais_192_207:
  {variar_octeto(16n, 192n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_192_207():
  {==}

law octetos_textuais_208_223:
  {variar_octeto(16n, 208n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_208_223():
  {==}

law octetos_textuais_224_239:
  {variar_octeto(16n, 224n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_224_239():
  {==}

law octetos_textuais_240_255:
  {variar_octeto(16n, 240n, [4, 0, 0, 0, 0, 0, 0, 0, 1], Nil{}) == True{} : Bool}
def octetos_textuais_240_255():
  {==}

law octetos_nomes_0_15:
  {variar_octeto(16n, 0n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_0_15():
  {==}

law octetos_nomes_16_31:
  {variar_octeto(16n, 16n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_16_31():
  {==}

law octetos_nomes_32_47:
  {variar_octeto(16n, 32n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_32_47():
  {==}

law octetos_nomes_48_63:
  {variar_octeto(16n, 48n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_48_63():
  {==}

law octetos_nomes_64_79:
  {variar_octeto(16n, 64n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_64_79():
  {==}

law octetos_nomes_80_95:
  {variar_octeto(16n, 80n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_80_95():
  {==}

law octetos_nomes_96_111:
  {variar_octeto(16n, 96n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_96_111():
  {==}

law octetos_nomes_112_127:
  {variar_octeto(16n, 112n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_112_127():
  {==}

law octetos_nomes_128_143:
  {variar_octeto(16n, 128n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_128_143():
  {==}

law octetos_nomes_144_159:
  {variar_octeto(16n, 144n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_144_159():
  {==}

law octetos_nomes_160_175:
  {variar_octeto(16n, 160n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_160_175():
  {==}

law octetos_nomes_176_191:
  {variar_octeto(16n, 176n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_176_191():
  {==}

law octetos_nomes_192_207:
  {variar_octeto(16n, 192n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_192_207():
  {==}

law octetos_nomes_208_223:
  {variar_octeto(16n, 208n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_208_223():
  {==}

law octetos_nomes_224_239:
  {variar_octeto(16n, 224n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_224_239():
  {==}

law octetos_nomes_240_255:
  {variar_octeto(16n, 240n, [6, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1], [0]) == True{} : Bool}
def octetos_nomes_240_255():
  {==}

def booleanos_iguais(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def valores_iguais(a: D.Valor, b: D.Valor) -> Bool:
  match a b:
    case D.VAusente{} D.VAusente{}:
      True{}
    case D.VBool{x} D.VBool{y}:
      booleanos_iguais(x, y)
    case D.VInt{ah, al} D.VInt{bh, bl}:
      U32.is_eq(ah, bh) && U32.is_eq(al, bl)
    case D.VTexto{x} D.VTexto{y}:
      String.eq(x, y)
    case D.VListaVazia{} D.VListaVazia{}:
      True{}
    case D.VLista{ah, at} D.VLista{bh, bt}:
      valores_iguais(ah, bh) && valores_iguais(at, bt)
    case D.VRegistroVazio{} D.VRegistroVazio{}:
      True{}
    case D.VRegistro{an, av, ar} D.VRegistro{bn, bv, br}:
      String.eq(an, bn) && valores_iguais(av, bv) && valores_iguais(ar, br)
    case _ _:
      False{}

def verificar_profundo(r: C.Resultado) -> Bool:
  match r:
    case C.Decodificado{v}:
      valores_iguais(v, aninhar(32n, D.VAusente{}))
    case _:
      False{}

def main() -> Bool:
  verificar_profundo(referencia(aninhar(32n, D.VAusente{})))
