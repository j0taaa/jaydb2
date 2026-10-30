# Provas gerais

`proof/VERIFICAR.bend` agrega as provas da implementação pura e a composição `ContratoServico.contrato_do_servico`, cujo alvo é exatamente `LAWS.Contrato(a,k)`. `tests/proof/VERIFICAR.bend` reaplica suas interfaces públicas em leis quantificadas. A conclusão para o servidor é condicional aos contratos explícitos das ferramentas e da integração Rust/Node/C; seus corpos não foram mecanizados em Bend.

- `Fundamentos`, `Ordens`, `Autenticacao`: estrutura e identidade autenticada.
- `Maquina`, `Seguranca`, `Preparacao`, `Publicacao`: percurso incremental, leis do administrador e preparação da proposta.
- `Chamada`: existência da preparação real após finalização e composição de execução autenticada/certificada com preparação fiel, conclusão válida e rollback. Usa as funções reais de `Nucleo`; não pressupõe fidelidade nem validade da conclusão.
- `Representacao`, `Transporte`, `RecepcaoLimites`, `Reificacao`: bytes, enquadramento e argumentos efetivos.
- `CodecVerificar`: 692 leis sobre o Codec original. `CodecLei2` demonstra que aceitação reconstitui a codificação original exata, que toda codificação representável dentro do teto é aceita e que o resultado satisfaz `Interface.DecodificacaoCorreta`, incluindo recusas.
- `EntradaVerificar`, `Configuracao`: composição da entrada real, autenticação, erros e configuração.
- `Recursos`, `AlocacoesComprimentos`, `ErrosFixos`: os três tamanhos lógicos e a conferência de comprimento anterior à construção. Não modelam memória física ou prazos.

## Conferência

```sh
make verify
```

O comando confere os hashes dos 18 originais e dos 14 módulos do contrato ativo, verifica os agregados positivos com `--check-only` e `--verdict` separados e executa seis negativos que removem premissas distintas: identidade, bytes, lei administrativa, publicação, comprimento e reificação. O timeout do runner serve apenas para interromper desenvolvimento travado.

Os exemplos fechados antigos e relatórios de rodadas anteriores foram retirados da suíte corrente; suas versões continuam no Git. Provas gerais não foram removidas para reduzir a contagem de linhas.

## Oito leis e fronteira confiável

O [mapa das oito leis](CONTRATO_SERVICO.md) identifica os oito termos usados na
composição, as funções reais a que se referem e os cinco grupos de premissas.
A validade do publicado, a identidade autenticada e a publicação correta são
conclusões; nenhuma das oito leis é recebida como premissa. `Processavel`
permanece externo e não é redefinido pelo sucesso do candidato.

A composição demonstra o núcleo e o protocolo serial. Sua aplicação ao
executável assume a correção das ferramentas oficiais e o refinamento dos
blocos concretos de fontes, processos, pipes, store e entrega, descritos no
mapa. Revisão e testes sustentam essa ligação operacional; não constituem uma
prova mecanizada de Rust/Node/C nem de todo o compilador. Não são admitidos
traços que omitam observações reais ou premissas de validade pós-publicação.
