#!/usr/bin/env bash
set -euo pipefail
project=$(cd "$(dirname "$0")" && pwd)
cd "${1:?expected path to dual-smale-global/lean}"
rev=8765ad9cf76ab041f49c287889096568f51df5d9
test "$(git rev-parse HEAD)" = "$rev"
python3 "$project/check_example.py"
lake exe cache get Mathlib.Tactic Mathlib.Analysis.Complex.CauchyIntegral Mathlib.Analysis.Complex.Schwarz Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv Mathlib.Analysis.Calculus.MeanValue Mathlib.Analysis.Complex.Polynomial.Basic Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic Mathlib.Algebra.Polynomial.Derivative Mathlib.Analysis.Complex.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real
lake build DualSmaleGlobal.UnconditionalAndGeometric
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -DwarningAsError=true "$project/Diameter.lean" | tee "$log"
python3 - "$log" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text()
for theorem in ("critical_chord_bound", "dual_smale_of_critical_chord"):
    pattern = rf"'DualSmaleDiameter\.{theorem}' depends on axioms:\s*\[([^\]]*)\]"
    match = re.search(pattern, text)
    if not match:
        sys.exit(f"missing axiom report for {theorem}")
    axioms = {name.strip() for name in match[1].split(",") if name.strip()}
    unexpected = axioms - {"propext", "Classical.choice", "Quot.sound"}
    if unexpected:
        sys.exit(f"{theorem} depends on unexpected axioms: {unexpected}")
PY
