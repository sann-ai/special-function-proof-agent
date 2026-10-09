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
              "gamma-ai-direct", "beta-ai-steps"):
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
