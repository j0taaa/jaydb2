# Native execution

Direct calls run one request in an official Bend executable. Prepared workers
stay alive across requests and exchange data operations with the host.
See [the native runtime guide](SIMPLE_RUNTIME.md) for the call path, ABI,
effects and trusted host duties.
