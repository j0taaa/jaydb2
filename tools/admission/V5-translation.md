# Candidato V5: equações, instâncias e fechamento

A revisão V4 encontrou três recusas de programas aceitos pelo Bend fixado:
equações perdidas ao abstrair um header, fechamento repetido por contagem de
eventos e aliases físicos rígidos no vínculo com a fonte. V1–V4 e seus relatórios
permanecem históricos. Esta implementação é candidata a nova revisão do root.

## Equações simbólicas

Um template `f : T` tem um item interno `f.template_body` de tipo
`Σ-fn:T -> Unit`, cujo primeiro campo contém a tradução da árvore `.e` original.
Esse campo é apagado. O kernel verifica seu tipo e corpo com suas regras
existentes; não há função arbitrária do tipo T assumida como hipótese.

Uma chamada aberta em contexto apagado projeta esse campo. Assim, uma prova
por casos pode reduzir o corpo de `f` no caso Zero e observar a chamada recursiva
no caso Succ. Isso se aplica também a domínios dependentes e a tipos de funções
ordinárias que contêm uma aplicação aberta de template. Se a conversão fecha os
argumentos, a chamada continua passando pelo resolvedor físico.

O item `.compile_schema : Unit` continua verificando seu payload tipado e
apagado. O pacote não entra em `book.tlds`; nenhuma árvore compilável o chama.
O kernel recusa projetar um campo q0 para uma prova viva. A regressão direta do
kernel exercita essa fronteira, e a regressão com corpo simbólico adulterado e
sem instâncias verifica
que um schema incorreto ainda é recusado sem depender de físicos/source_links.

## Resolução física e vínculo com a fonte

O adaptador de `def_inst` conserva o `tele_check` original. Seu cache pode
reutilizar uma declaração física existente quando os argumentos passam pelo
`term_compare("EQ")` original. O preparador e Safe usam esse mesmo resolvedor.
Não se acrescenta igualdade nem regra de checagem. Uma chave exata existente
conserva seu Def; argumentos apenas convertíveis não geram entradas adicionais
a cada anotação reconstruída. Físicos já presentes não são fundidos.

Para cada físico, uma árvore esperada separada é elaborada por `def_check` a
partir da fonte e argumentos registrados. O corpo físico não é sua fonte nem
é sobrescrito por ela. Se a re-elaboração escolheu outro alias na mesma posição,
a Ref esperada só pode usar a Ref física após conferir a mesma origem de
template e a igualdade original de todos os argumentos. Todo o restante da
árvore esperada vem da elaboração da fonte.

Todas as declarações físicas permanecem raízes vivas e cada uma tem seu próprio
vínculo de origem, inclusive aliases preexistentes e instâncias da Base. Uma
alteração no corpo de qualquer alias precisa passar por esse guard e pela
checagem viva. Não há um fallback de especialização lógica `.qv` para chamadas
fechadas. A tradução das chamadas reais conserva o nome físico que o compilador
referencia; o alinhamento de aliases acontece somente na árvore esperada do
guard.

## Estado final e prazo

O fechamento compara o grafo preparado antes e depois da rechecagem original e
do fechamento final. `rewrites` não é um critério de progresso: o primário pode
reconstruir uma anotação que volta ao mesmo estado preparado. Inventário e
metadados fazem parte do selo. Novas instâncias exigem nova rodada.

A auditoria final de capacidades e o primário final precedem o BendTT. A emissão
recebe o mesmo Book e não pode criar novas declarações. Os retries de fuel
conservam esse fechamento, os bytes e o prazo original do host, sem teto de
tentativas nem renovação do prazo.

As fontes oficiais, leis, regras, axiomas e kernel Lean não foram alterados.
As regressões e os hashes são evidência de implementação; não constituem uma
prova geral da tradução ou do Contrato/MedicaoReal. A revisão V5 é independente
e permanece responsabilidade do root.
