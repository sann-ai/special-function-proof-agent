# Saved proof examples

This directory contains 157 replayable certificates: 155 complete proofs and two
historical conditional certificates. Each run keeps its fixed request, generated
Lean certificate, standard-axiom audit, numerical diagnostic and result.

After building the base project and its analytic definitions, recheck all evidence:

```sh
lake build
lake build SpecialFunctionProofAgent.AnalyticDefinitions SpecialFunctionProofAgent.UserAnalyticDefinitions SpecialFunctionProofAgent.AdvancedAnalyticDefinitions
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

The twelve `user-*` runs use user-specified factorial-kernel combinations,
polynomial integrands with real endpoints, and polynomial-coefficient homogeneous
ODEs with initial conditions. Each class includes both proof routes and both routes
of source-lemma application to a different target. The generated bridges check the
original user expression against its normalization and retain its analytic contract.
See [user expression syntax and examples](../docs/research-user-analytic-definitions.md).

`cross-product` and `integer-y-recurrence` preserve their original conditional
scope and premises. Complete proofs of their corresponding supported targets are
saved separately, including `cross-product-root-*` and `integer-y-complete-*`.
Personal inputs and archives belong outside this repository.

The sixteen `advanced-*` runs cover bounded geometric series, affine exp/sin/cos
integrals, nonlinear sqrt-state IVPs, and polynomial second-order forcing. Each
class includes direct/steps source and distinct-target lemma proofs. Five plans
were generated through Codex; their verified evidence is retained alongside
local deterministic plans. See [the exact input classes](../docs/research-advanced-analytic-definitions.md).
