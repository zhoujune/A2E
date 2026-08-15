#!/usr/bin/env bash
set -euo pipefail

repo_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
report_path="${PROVEAI_K4_I1_REPORT:-$repo_root/reference-broker/evaluation/results/k4-i1-submission.json}"
iterations="${PROVEAI_K4_I1_ITERATIONS:-100}"

case "$iterations" in
    ''|*[!0-9]*)
        echo "PROVEAI_K4_I1_ITERATIONS must be a positive integer" >&2
        exit 2
        ;;
esac
if [ "$iterations" -eq 0 ]; then
    echo "PROVEAI_K4_I1_ITERATIONS must be positive" >&2
    exit 2
fi

export PROVEAI_K4_I1_ITERATIONS="$iterations"
export PROVEAI_K4_I1_REPORT="$report_path"

# The shared harness retains the earlier K4-I0 traces and additionally runs the
# fail-closed submission profile. There is no ungated evaluation branch here.
/usr/bin/bash "$repo_root/artifact/run-k4-i0.sh"

test -s "$report_path"
python3 "$repo_root/reference-broker/evaluation/validate_k4_i1.py" "$report_path"
echo "K4-I1 retained submission evaluation: $report_path"
