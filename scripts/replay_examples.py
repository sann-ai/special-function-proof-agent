"""Recheck committed AI proof plans without invoking AI or reading credentials."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from special_function_agent.core import replay

for route in ("direct", "steps", "recurrence-direct", "recurrence-steps", "calculus-direct", "calculus-steps",
              "origin-direct", "origin-steps", "gamma-direct", "gamma-steps",
              "beta-direct", "beta-steps", "scaled-gamma-direct", "scaled-gamma-steps",
              "gamma-ai-direct", "beta-ai-steps",
              "hermite-h-derivative-direct", "hermite-h-derivative-steps",
              "hermite-he-derivative-direct", "hermite-he-derivative-steps",
              "hermite-h-zero-direct", "hermite-h-zero-steps", "hermite-h-one-direct", "hermite-h-one-steps",
              "hermite-he-zero-direct", "hermite-he-zero-steps", "hermite-he-one-direct", "hermite-he-one-steps",
              "hermite-h-recurrence-direct", "hermite-h-recurrence-steps",
              "erf-derivative-direct", "erf-derivative-steps", "erf-zero-direct", "erf-zero-steps",
              "erf-odd-direct", "erf-odd-steps", "gaussian-finite-integral-direct", "gaussian-finite-integral-steps",
              "hermite-ai-direct", "erf-ai-steps",
              "legendre-parity-direct", "legendre-parity-steps",
              "legendre-zero-direct", "legendre-zero-steps",
              "legendre-one-direct", "legendre-one-steps",
              "legendre-two-direct", "legendre-two-steps",
              "legendre-right-direct", "legendre-right-steps",
              "legendre-left-direct", "legendre-left-steps",
              "laguerre-zero-direct", "laguerre-zero-steps",
              "laguerre-one-direct", "laguerre-one-steps",
              "laguerre-two-direct", "laguerre-two-steps",
              "ordinary-laguerre-one-direct", "ordinary-laguerre-one-steps",
              "ordinary-laguerre-two-direct", "ordinary-laguerre-two-steps",
              "laguerre-derivative-direct", "laguerre-derivative-steps",
              "jacobi-zero-direct", "jacobi-zero-steps",
              "jacobi-one-direct", "jacobi-one-steps",
              "jacobi-two-direct", "jacobi-two-steps",
              "jacobi-derivative-direct", "jacobi-derivative-steps",
              "jacobi-legendre-direct", "jacobi-legendre-steps",
              "yhalf-recurrence-direct", "yhalf-recurrence-steps",
              "yhalf-derivative-direct", "yhalf-derivative-steps",
              "laguerre-ai-direct", "yhalf-ai-steps",
              "legendre-recurrence-direct", "legendre-recurrence-steps",
              "legendre-adjacent-integral-direct", "legendre-adjacent-integral-steps",
              "laguerre-recurrence-direct", "laguerre-recurrence-steps",
              "legendre-recurrence-ai-direct", "legendre-adjacent-integral-ai-steps",
              "legendre-orthogonal-direct", "legendre-orthogonal-steps",
              "legendre-norm-direct", "legendre-norm-steps",
              "integer-y-complete-direct", "integer-y-complete-steps",
              "legendre-orthogonal-ai-steps", "integer-y-complete-ai-direct",
              "integer-y-zero-derivative-direct", "integer-y-zero-derivative-steps",
              "integer-y-one-derivative-direct", "integer-y-one-derivative-steps",
              "integer-y-wronskian-direct", "integer-y-wronskian-steps",
              "integer-y-cross-same-point-direct", "integer-y-cross-same-point-steps",
              "cross-product-root-direct", "cross-product-root-steps",
              "integer-y-derivative-ai-direct", "cross-product-root-ai-steps",
              "research-gamma-direct", "research-gamma-steps", "research-gamma-four-direct"):
    path = ROOT / "demo" / route / "request.json"
    if not path.exists():
        raise SystemExit(f"Missing saved proof plan: {path}")
    result = replay(path.parent, timeout=120)
    print(f"Saved {route}: {result['status']}")
    if result["status"] != "proved" or not result["replayed"]:
        raise SystemExit(json.dumps(result, ensure_ascii=False))

conditional = replay(ROOT / "demo/cross-product", timeout=120)
print("Cross-product conditional algebra:", conditional['conditional_replayed'])
if not conditional.get('conditional_replayed') or conditional.get('full_bessel_proof') is not False:
    raise SystemExit(json.dumps(conditional, ensure_ascii=False))

integer_y = replay(ROOT / "demo/integer-y-recurrence", timeout=120)
print("Integer-Y recurrence under explicit order differentiability:", integer_y['conditional_replayed'])
if not integer_y.get('conditional_replayed') or integer_y.get('full_bessel_proof') is not False:
    raise SystemExit(json.dumps(integer_y, ensure_ascii=False))
