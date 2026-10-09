"""Audit the fixed public special-function API with the verifier's axiom policy."""
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from special_function_agent import core


# Explicit public API inventory. Add each new exported definition or theorem here.
PUBLIC_DECLARATIONS = {
    "Gamma": (
        "gamma_recurrence",
        "gamma_scaled_integral",
    ),
    "Beta": (
        "beta_integral_ofReal",
        "beta_integral",
    ),
    "Hermite": (
        "hermiteHe",
        "hermiteH",
        "hermiteH_eq_scaled_hermiteHe",
        "hasDerivAt_hermiteHe_succ",
        "hermiteHe_derivative",
        "hermiteHe_zero",
        "hermiteHe_one",
        "hermiteH_zero",
        "hermiteH_one",
        "hasDerivAt_hermiteH_succ",
        "hermiteH_derivative",
        "hermiteHe_succ_succ",
        "hermiteH_succ_succ",
        "hermiteH_recurrence",
    ),
    "Erf": (
        "erf",
        "hasDerivAt_erf",
        "deriv_erf",
        "erf_zero",
        "erf_neg",
        "gaussian_integral",
    ),
    "PolynomialSeries": (
        "hasDerivAt_finitePowerSeries",
    ),
    "Legendre": (
        "legendreP",
        "legendreP_shifted",
        "legendreP_finite_sum",
        "legendreP_zero",
        "legendreP_one",
        "legendreP_two",
        "legendreP_neg",
        "legendreP_at_one",
        "legendreP_at_neg_one",
    ),
    "Laguerre": (
        "laguerreL",
        "laguerreL_finite_sum",
        "laguerreL_zero",
        "laguerreL_one",
        "laguerreL_two",
        "laguerreL_at_zero",
        "laguerreL_ordinary_at_zero",
        "hasDerivAt_laguerreL_succ",
        "laguerreL_derivative",
    ),
    "Jacobi": (
        "jacobiP",
        "jacobiP_finite_sum",
        "jacobiP_zero",
        "jacobiP_one",
        "jacobiP_two",
        "jacobiP_at_one",
        "hasDerivAt_jacobiP_succ",
        "jacobiP_derivative",
        "jacobiP_zero_zero",
        "jacobiP_legendre_zero",
        "jacobiP_legendre_one",
        "jacobiP_legendre_two",
    ),
    "BesselY": (
        "realBesselJ",
        "besselYNoninteger",
        "besselYInt",
        "sin_order_pi_ne_zero_iff",
        "ofReal_realBesselJ",
        "realBesselJ_neg_int",
        "ofReal_besselYNoninteger",
        "besselYNoninteger_connection",
        "realBesselJ_recurrence",
        "hasDerivAt_realBesselJ",
        "besselYNoninteger_neg",
        "besselYNoninteger_recurrence",
        "hasDerivAt_besselYNoninteger",
        "deriv_besselYNoninteger",
        "besselYNoninteger_ode",
        "besselYInt_zero",
        "besselYInt_one",
        "besselYInt_two",
        "besselYInt_neg",
        "besselYNoninteger_half",
        "sin_half_order_pi_ne_zero",
        "Yhalf_recurrence",
        "hasDerivAt_Yhalf",
        "Yhalf_derivative",
        "tendsto_besselYNoninteger_int_of_differentiable_order",
    ),
}


def audit() -> dict[str, list[str]]:
    names = [f"SpecialFunctionProofAgent.{name}"
             for group in PUBLIC_DECLARATIONS.values() for name in group]
    if len(names) != len(set(names)):
        raise core.InputError("The public declaration inventory contains duplicates.")
    lines = [f"import SpecialFunctionProofAgent.{module}" for module in PUBLIC_DECLARATIONS]
    # The existing runner checks this one target; each public declaration is then
    # checked separately below with the same strict audit parser and axiom policy.
    lines += [f"theorem {core.THEOREM} : True := True.intro",
              '#eval IO.println "BESSEL_AUDIT_BEGIN"',
              f"#print axioms {core.THEOREM}",
              '#eval IO.println "BESSEL_AUDIT_END"']
    for index, name in enumerate(names):
        lines += [f'#eval IO.println "SPECIAL_AUDIT_{index}_BEGIN"',
                  f"#print axioms {name}",
                  f'#eval IO.println "SPECIAL_AUDIT_{index}_END"']
    scratch = ROOT / ".lake/special-function-scratch"
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="public-axioms-", dir=scratch) as temporary:
        source = Path(temporary) / "PublicAxioms.lean"
        source.write_text("\n".join(lines) + "\n", encoding="utf-8")
        result = core._run_lean(source, timeout=120)
    if not result["accepted"]:
        raise core.InputError(f"Public API audit failed: {result}")
    stdout = result["stdout"]
    audited = {}
    for index, name in enumerate(names):
        begin, end = f"SPECIAL_AUDIT_{index}_BEGIN", f"SPECIAL_AUDIT_{index}_END"
        if stdout.count(begin) != 1 or stdout.count(end) != 1:
            raise core.InputError(f"Missing or repeated dependency audit for {name}.")
        body = stdout.split(begin, 1)[1].split(end, 1)[0].strip()
        if not body.startswith(f"'{name}' "):
            raise core.InputError(f"Unexpected dependency audit for {name}: {body}")
        # Only the exact declaration label changes; the complete dependency
        # output still passes through core.audit_axioms without filtering.
        body = body.replace(f"'{name}'", f"'{core.THEOREM}'", 1)
        audited[name] = core.audit_axioms(
            f"BESSEL_AUDIT_BEGIN\n{body}\nBESSEL_AUDIT_END")
    return audited


def main() -> None:
    try:
        audited = audit()
    except core.InputError as exc:
        raise SystemExit(str(exc)) from exc
    for module, names in PUBLIC_DECLARATIONS.items():
        print(f"{module}: {len(names)} public declarations audited")
    dependencies = sorted({axiom for axioms in audited.values() for axiom in axioms})
    print(f"PASS: {len(audited)} public definitions/theorems; dependencies: "
          + ", ".join(dependencies))


if __name__ == "__main__":
    main()
