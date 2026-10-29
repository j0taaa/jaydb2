# Limite de cada leitura confirmada

`RecepcaoLimites.bend` prova seis leis gerais. O parâmetro `cap` é qualquer
Nat, inclusive zero: não acrescenta uma quota de mensagem ou do programa.
O leitor pode dividir uma mensagem em qualquer número de chunks.

`consumo_confirmado_respeita_declarado_e_limite` recebe o total anterior dentro
do tamanho declarado, sua admissão no teto da mensagem e uma quantidade real
no máximo igual ao request `min(cap, declarado - antes)`. Demonstra que o novo
total não ultrapassa o declarado nem o teto. As comparações são inclusivas.
Transitividade, limite do mínimo e subtração natural são demonstrados por
indução, sem assumir essas desigualdades finais.

`cabecalho_medido_estabelece_declaracao_original` liga `nat64(declarado)` às
palavras alta/baixa do cabeçalho e demonstra o predicado original de igualdade
da declaração. `consumo_real_limitado_estabelece_regra2_original` compõe essas
relações e produz exatamente `LAWS.Regra2(LeuCorpo{antes, recebido, declarado})`
num cenário de atendimento, sem receber a própria Regra2 como premissa.
O teste positivo reaplica essa API para todo corpo, cabeçalho representável,
configuração e quantidade confirmada. Duas mutações recusam consumo além do
restante e substituição do tamanho do cabeçalho.

A quantidade confirmada é uma obrigação de correspondência com o `read` real.
O teorema não afirma que um número escrito num recibo satisfaz esse contrato.
O C selecionado retém o retorno real antes de FFI, limita o request ao restante
e não repete um recibo usado. A ponte ainda precisa ligar cada chamada e seu
recibo ao evento real, incluindo o total anterior, a identidade do frame,
consumo único e validade da recepção inteira. `RecepcaoValida` não é concluída
da desigualdade: bytes, comprimento efetivo, framing e truncamento têm suas
próprias obrigações.

Uma exceção Python não prova consumo zero. Uma repetição exige que o leitor preserve corretamente o consumo confirmado.
Progresso do driver e correspondência dos fatos externos não são resultados
desta prova. O contrato ativo não exige medição ou orçamento físico. Nenhum `Ambiente` foi criado, e não há
alegação de Lei2 completa ou Contrato do executável.
