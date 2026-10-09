# Special Function Proof Agent: Codex instructions

These rules apply throughout this project.

- Preserve the exact input target: variable names and types, bindings, all assumptions, function definitions and conventions. Ask for a missing mathematical condition before adopting it.
- Parse text with `python3 -m special_function_agent parse`; inspect the saved target before proposing a proof plan.
- Use `verify --route direct` or `verify --route steps` for the local registered Gamma/Beta/Hermite/erf recipes. Use `python3 -m special_function_agent.generate ... --route direct|steps` for a Codex-generated plan.
- Hermite H uses the physicists convention; He uses the probabilists convention. Require natural degree and the stated lower bound for a predecessor degree. Bessel degree n remains integer. Erf and its Gaussian finite-interval formulas use all real arguments/endpoints.
- The verifier owns the theorem and the Lean translation. A proof candidate contains only the closed recipe/step schema; it cannot replace a target, add assumptions, or submit arbitrary Lean code.
- Keep the original theorem, conditional algebra, and numerical diagnostics separate. Report `proved` only after the fixed full target passes Lean and the standard-axiom audit.
- Bessel Y and cross-product analysis remains `unresolved`, with `full_bessel_proof: false`; the conditional certificate proves the explicitly listed algebraic statement.
- Use only `propext`, `Classical.choice`, and `Quot.sound`. Preserve the `sorry` and dependency audit.
- Archive data belongs outside this repository, by default in `~/SpecialFunctionProofAgentData/archive`. Recheck saved certificates against the current mathematical environment before reuse.
- Import Bessel evidence only through explicit `archive import-bessel`; preserve source environment and provenance and reverify in this project.
- The numerical backend is optional. When existing mpmath is unavailable, save `backend_unavailable` and continue supported symbolic/formal checks. Do not install dependencies without authorization.
- Keep changes small. Run focused tests, then `SF_RUN_LEAN_TESTS=1 BESSEL_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -v`, `lake build`, and `python3 scripts/replay_examples.py` for release validation.
- Keep user inputs, private archives, credentials, generated local runs and account metadata out of Git.
