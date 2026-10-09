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
              "hermite-ai-direct", "erf-ai-steps"):
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
