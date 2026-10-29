# Recursos simples para a primeira versão funcional

Proposta concreta, ainda sem alterar os 18 arquivos originais ou ativar outra
versão das oito leis. Responde à orientação do usuário de 2026-10-29: priorizar
a primeira versão funcional e a correspondência entre prova e execução;
simplificar recursos mesmo permitindo consumo e duração excessivos. Depois da
primeira versão, simplificar o código preservando o contrato então aprovado.

## Uma alteração formal necessária

Em `contrato/LAWS.bend`, `Regra2`, o caso `AlocouCampo` atualmente exige
simultaneamente comprimento conferido e memória física dentro do teto:

```bend
case I.AlocouCampo{pos, n, memoria}:
  L.E<I.Antes(a, k, x, t, I.ConferiuComprimento{pos, n}),
    {Nat.is_le(memoria, X.limite(I.configuracao(x), X.Memoria{})) == True{} : Bool}>
```

A proposta substitui SOMENTE esse caso por:

```bend
case I.AlocouCampo{pos, n, memoria}:
  I.Antes(a, k, x, t, I.ConferiuComprimento{pos, n})
```

O excesso de memória deixa de violar a Lei 2. A conferência do comprimento
continua obrigatória. Os demais casos da Lei 2 e as Leis 1, 3, 4, 5, 6, 7 e 8
não são enfraquecidos. A implementação não poderá afirmar o contrato original
com a antiga garantia física; a variante aprovada deverá ser identificada
expressamente. O original permanece como histórico autenticado.

Não é necessário apagar da Lei 7 a exigência de medidas e causas verdadeiras.
Quando houver resposta `limite`, sua causa continuará sendo um limite lógico
verificado ou um prazo realmente observado. Falta de memória real é falha de
execução, não autorização para inventar uma medição. As regras atuais não
exigem uma medição periódica de toda a memória nem um teto fixo de latência de
interrupção. Elas também não exigem que se interrompa uma computação somente
porque um prazo passou sem ter sido observado num ponto seguro.

## Comportamento proposto

- Mensagem, estado publicado e resposta mantêm os limites lógicos exatos.
- Memória de processamento deixa de ter garantia de um teto global exato.
  Não haverá observador `ptrace`, congelamento de toda a árvore de processos,
  deduplicação de mappings ou protocolo N2 na entrada simples.
- Prazos usam o relógio monotônico e checagens cooperativas já disponíveis.
  Auxiliares podem ser encerrados quando o host observa seu prazo. Nenhuma
  promessa de preempção geral ou recuperação de toda falta de memória é feita.
- Código pode consumir mais memória ou durar mais que o orçamento pretendido.
  Uma falha que inutilize o processo pode encerrar a instância e perder o banco
  em RAM. Isso nunca vira uma publicação parcial ou uma prova dispensada.
- A correspondência fonte/prova/programa, a autenticação, as leis do
  administrador e a publicação inteira permanecem requisitos centrais.

## Ordem de trabalho

As frentes experimentais de contabilidade física exata e instrumentação de
campos por causa dessa contabilidade foram interrompidas. Seus arquivos e
resultados ficam preservados como histórico, fora do caminho da primeira
versão. Não se substituirá `INCOMPLETE` por uma alegação de cobertura completa.

Primeiro: fechar a correspondência de Bend, usar o Codec original compilado,
consolidar a entrada simples e verificar casos reais completos. Depois:
reduzir módulos, interfaces e duplicações sem enfraquecer o contrato aprovado.

Esta proposta depende da confirmação pontual pedida pelo usuário para
alterações de leis. Até lá, nenhum arquivo original ou predicado de lei foi
modificado.
