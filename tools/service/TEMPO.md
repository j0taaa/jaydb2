> Histórico anterior à retirada autorizada dos orçamentos físicos. Este mecanismo não integra o serviço ativo; veja `../../PROPOSTA_RECURSOS_SIMPLES.md` e `../../native/SIMPLE_RUNTIME.md`. O texto e os resultados abaixo pertencem ao escopo anterior.

# Tempo por etapa: decisão do ambiente

Em 2026-10-29, o usuário escolheu explicitamente **primeira checagem segura**:
tempo decorrido em `CLOCK_MONOTONIC`, sem teto rígido de latência de
interrupção do Linux. As oito leis e os cinco orçamentos originais continuam
intactos. Esse esclarecimento está incorporado em `ESPECIFICACAO.md`; a
cópia original e os arquivos Bend do contrato permanecem preservados.

Para início `s` e orçamento positivo `b`, a quantidade medida é
`agora - s`, com `agora >= s`. O prazo vence com `agora >= s + b`.
Igualdade já é vencimento temporal; memória exige excesso estrito. A mesma
origem acompanha o frontend, as tentativas de kernel/modelo, execução,
preparação e seus recibos. Uma nova tentativa ou a recuperação de um wrapper
não ganha um novo orçamento.

A próxima checagem segura que constata o vencimento interrompe a computação
da etapa. Não se exige uma constante adicional `K` que limite o atraso físico
de agendamento ou de retorno de uma syscall. Referências históricas a essa
exigência nos snapshots não representam uma nova cota pública do banco.

Isso não resolve automaticamente progresso ou ownership: uma operação em
andamento, mm emprestado por vfork ou metadado crítico pendente não pode ser
tratado como cancelado só porque o relógio venceu. Os efeitos reais já
commitados precisam ser reconciliados. Cleanup não autoriza resposta ou
publicação enquanto owners indispensáveis estiverem incertos. Uma espera
sem mecanismo de progresso demonstrado continua uma obrigação, sem ser
reclassificada como falha ambiental inventada.

As guardas anteriores à construção de Campo e à publicação continuam
obrigatórias em suas fronteiras reais. A decisão não permite observar o
vencimento e continuar publicando, usar uma medida antiga como nova, limpar
`INCOMPLETE` ou apresentar um recibo de controle como `MedicaoReal`.

`proof/PrazosMedidos.bend` demonstra a ligação aritmética ao tipo temporal
original e que renovar o epoch oculta expiração. `PreparacaoTemporal.bend`
justifica `Preparou` por uma medida temporal real, sem premissa de cobertura
de memória; não demonstra cleanup, conclusão ou implementação dos relógios.
O N1 do observer e o protótipo N2 ainda precisam de integração ao host.
