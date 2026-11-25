#!/bin/sh
set -eu
PNP_RESEARCH_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$PNP_RESEARCH_ROOT/lean"
export LEAN_PATH="$PNP_RESEARCH_ROOT${LEAN_PATH:+:$LEAN_PATH}"
lake build PEqualNP.MetaComplexity.Helpers.RepPath
for PNP_RESEARCH_MODULE in OneNotObservations Threshold16 Lower89 OneNotCircuitReplacement; do
  lake env lean --root="$PNP_RESEARCH_ROOT" \
    -o "$PNP_RESEARCH_ROOT/research/$PNP_RESEARCH_MODULE.olean" \
    "$PNP_RESEARCH_ROOT/research/$PNP_RESEARCH_MODULE.lean"
done
lake env lean --stdin <<'EOF'
import research.Lower89
import research.Threshold16
import research.OneNotCircuitReplacement
#print axioms lower90
#print axioms threshold16_replaces_large
#print axioms OneNotCircuitReplacement.replace_by_true
#print axioms OneNotCircuitReplacement.replace_by_false
EOF
