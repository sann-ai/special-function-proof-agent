# Saved proof examples

This directory contains 129 replayable certificates: 127 complete proofs and two
historical conditional certificates. Each run keeps its fixed request, generated
Lean certificate, standard-axiom audit, numerical diagnostic and result.

After building the base project and its analytic definitions, recheck all evidence:

```sh
lake build
lake build SpecialFunctionProofAgent.AnalyticDefinitions
python3 scripts/replay_examples.py
```

Reverification requires no AI authentication. Runs with `generation.json` retain
metadata for candidates generated through Codex CLI with Ultra; the other plans
use the local closed proof recipes.

The twelve `analytic-*` runs cover the factorial exponential series, the oriented
Gaussian primitive, and the global homogeneous real initial-value problem. Each
has direct/steps source proofs and direct/steps applications of the registered
source lemma to a different target. Definitions, analytic contracts, dependency
IDs and the optional analytic-module hash stay with the fixed request and result.
See [the definitions and CLI examples](../docs/research-analytic-definitions.md).

`cross-product` and `integer-y-recurrence` preserve their original conditional
scope and premises. Complete proofs of their corresponding supported targets are
saved separately, including `cross-product-root-*` and `integer-y-complete-*`.
Personal inputs and archives belong outside this repository.
