#!/usr/bin/env python3
"""Validate coverage and required explanations in the RQ4 matrix."""

import json
import sys
from pathlib import Path


ADAPTERS = {"Uncontrolled", "Idempotent", "Deduplicated"}
WINDOWS = {
    "reservation_to_send",
    "send_to_linearization",
    "linearization_to_delivery",
    "delivery_to_persistence",
    "persistence_to_terminalization",
    "recovery_interruption",
}
CLASSIFICATIONS = {"safe_completion", "unknown", "assumption_dependent"}
CELL_KEYS = {
    "adapter",
    "fault_window",
    "m4_evidence",
    "classification",
    "recovery_action",
    "safety_basis",
    "availability_tradeoff",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_rq4.py MATRIX.json")
    path = Path(sys.argv[1])
    with path.open("r", encoding="utf-8") as stream:
        matrix = json.load(stream)
    require(matrix["schema_version"] == 1, "unsupported schema version")
    require(isinstance(matrix["scope"], str) and matrix["scope"], "missing scope")
    require(set(matrix["classification_legend"]) == CLASSIFICATIONS, "legend mismatch")
    require(
        set(matrix["global_outcome_rules"])
        == {"conclusive_failure", "invalid_result", "retry_exhaustion"},
        "global outcome rules mismatch",
    )
    cells = matrix["cells"]
    require(isinstance(cells, list) and len(cells) == 18, "matrix must contain 18 cells")
    seen = set()
    for index, cell in enumerate(cells):
        require(set(cell) == CELL_KEYS, f"cell {index} keys mismatch")
        require(cell["adapter"] in ADAPTERS, f"cell {index} adapter mismatch")
        require(cell["fault_window"] in WINDOWS, f"cell {index} window mismatch")
        require(cell["classification"] in CLASSIFICATIONS, f"cell {index} classification mismatch")
        for field in ("m4_evidence", "recovery_action", "safety_basis", "availability_tradeoff"):
            require(isinstance(cell[field], str) and cell[field], f"cell {index} missing {field}")
        pair = (cell["adapter"], cell["fault_window"])
        require(pair not in seen, f"duplicate matrix pair: {pair}")
        seen.add(pair)
    expected = {(adapter, window) for adapter in ADAPTERS for window in WINDOWS}
    require(seen == expected, "adapter/window coverage mismatch")
    print(f"validated RQ4 matrix: {path}")


if __name__ == "__main__":
    main()
