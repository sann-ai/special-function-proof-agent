# Special Function Proof Agent: Codex instructions

These rules apply throughout this project.

- Preserve the exact input target: variable names and types, bindings, all assumptions, function definitions and conventions. Ask for a missing mathematical condition before adopting it.
- Parse text with `python3 -m special_function_agent parse`; inspect the saved target before proposing a proof plan.
- Use `verify --route direct` or `verify --route steps` for the local registered Gamma/Beta/Hermite/erf, Legendre/Laguerre/Jacobi and half-integer YNoninteger recipes. Use `python3 -m special_function_agent.generate ... --route direct|steps` for a Codex-generated plan.
- Hermite H uses the physicists convention; He uses the probabilists convention. Hermite/Legendre/Laguerre/Jacobi require natural degree and the stated lower bound for a predecessor degree. Bessel degree variable n remains integer. Preserve all real polynomial parameters and the alpha=0 ordinary Laguerre convention; see [orthogonal polynomial definitions](docs/orthogonal-polynomials.md) and [recurrences and adjacent orthogonality](docs/polynomial-calculus.md). Erf and its Gaussian finite-interval formulas use all real arguments/endpoints.
- A derivative fixes every other free real variable. Preserve parameter dependence and use distinct generated binders for nested derivatives and integrals.
- The verifier owns the theorem and the Lean translation. A proof candidate contains only the closed recipe/step schema; it cannot replace a target, add assumptions, or submit arbitrary Lean code.
- Keep the original theorem, explicitly conditional analytic/algebraic certificates, and numerical diagnostics separate. Report `proved` only after the fixed full target passes Lean and the standard-axiom audit.
- The explicit `YNoninteger` AST supports orders -1/2, 1/2, 3/2 and x>0 for the registered recurrence and derivative. Full Lean acceptance sets `full_bessel_proof: true`. Legacy Y and cross-product analysis remains `unresolved`, with `full_bessel_proof: false`; conditional certificates retain their fixed scope and every listed premise. Integer-Y recurrence needs explicit order differentiability at 0 and 1; preserve these as outstanding obligations in reports and archives. The integer-Y limit bridge retains explicit order-differentiability premises; see [Bessel Y scope](docs/bessel-y-formalization.md).
- Use only `propext`, `Classical.choice`, and `Quot.sound`. Preserve the `sorry` and dependency audit.
- Archive data belongs outside this repository, by default in `~/SpecialFunctionProofAgentData/archive`. Recheck saved certificates against the current mathematical environment before reuse.
- Import Bessel evidence only through explicit `archive import-bessel`; preserve source environment and provenance and reverify in this project.
- The numerical backend is optional. When existing mpmath is unavailable, save `backend_unavailable` and continue supported symbolic/formal checks. Do not install dependencies without authorization.
- Keep changes small. Run focused tests, then `SF_RUN_LEAN_TESTS=1 BESSEL_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -v`, `lake build`, `python3 scripts/audit_special_functions.py`, and `python3 scripts/replay_examples.py` for release validation.
- Keep user inputs, private archives, credentials, generated local runs and account metadata out of Git.
