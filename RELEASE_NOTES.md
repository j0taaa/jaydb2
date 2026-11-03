# 0.1.0 — versão experimental

Banco em RAM serial por stdin/stdout: host Rust, admissão Node e executáveis
convencionais gerados pelo Bend 2.0.39 oficial. Três limites lógicos de tamanho;
sem contabilidade física ou prazo próprio por requisição.

## Percurso utilizável

[INSTALL.md](INSTALL.md) descreve instalação local, ferramentas, download do
BendTT fixado e execução de `make demo`. A aplicação de credenciais usa leis
reais de leitura/escrita por identidade, prova universal e publicação no
servidor real. A sessão demonstra sucesso, autenticação e rollback de recusa.

## Revisão e simplificação desta versão

Dois subagentes revisaram separadamente a ligação Rust/C e a admissão/compilação
Node, sem editar o candidato ou executar novas suítes. Não encontraram defeito
concreto nos recortes examinados. A revisão confirmou as correspondências
entre fontes/metadados, snapshot privado, passos, processo recolhido, proposta
inteira, store e entrega descritas em
[CONTRATO_SERVICO.md](proof/CONTRATO_SERVICO.md). Isso é evidência de revisão,
não uma prova mecanizada da integração.

Uma terceira auditoria identificou quatro cortes locais: parâmetros sem uso no
verificador e na caminhada de loops, parse duplicado do diagnóstico e uma
asserção de runtime repetida. Os testes de fronteiras diferentes foram
preservados. Não foi criada uma segunda implementação ou nova suíte paralela.

## Garantias e limites

`ContratoServico.contrato_do_servico` reúne exatamente as oito leis, sob os
contratos explícitos das ferramentas e integração. Rust/Node/C, Clang, sistema
operacional e preservação semântica das ferramentas oficiais fazem parte da
base confiável. A revisão e os testes não eliminam essas hipóteses.

A instância pode ser perdida com o processo. Não há persistência, listener de
rede ou concorrência entre transações. As limitações oficiais observadas de
Nat/Array permanecem [documentadas](native/SIMPLE_RUNTIME.md); o JayDB não
modifica Bend para contorná-las. Compilação e provas podem consumir muitos
recursos ou demorar; disponibilidade não é garantida por quotas próprias.

## Verificação da versão

```sh
make build
make verify-contract
make verify
make test
make demo
```

A instalação também é exercitada em diretório novo, sem `.tools` ou `target`
preexistentes, usando fontes e distribuições baixadas e o BendTT fixado. Os
comandos acima são os mesmos mantidos no projeto; não há uma suíte especial
que substitua a validação normal.
