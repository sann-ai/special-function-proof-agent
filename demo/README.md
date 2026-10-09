# Saved proof examples

The eight Bessel examples retain their original generated plans from the upstream
project and have been reverified in this independent mathematical environment.
The six Gamma/Beta examples use the local registered direct/steps plans; their
request, actual Lean certificate, axiom audit, numerical diagnostics and result
are saved together.

Run `python3 scripts/replay_examples.py` after `lake build` to recheck all 16
certificates. This operation requires no AI authentication.

The Gamma direct and Beta steps AI examples were generated through Codex CLI
with Ultra and verified in this project. The cross-product example retains an
unresolved full Bessel theorem alongside accepted conditional algebra and nine
numerical root samples.

New AI-generated plans can be created with `python3 -m special_function_agent.generate`.
Personal inputs and archives are excluded from this directory.
