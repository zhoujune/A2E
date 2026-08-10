#!/usr/bin/env bash
set -euo pipefail

repo_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${VERUS_BIN:?set VERUS_BIN to the pinned Verus executable}"
: "${RUSTC:?set RUSTC to the toolchain rustc used by Verus}"
: "${VERUS_Z3_PATH:?set VERUS_Z3_PATH to the pinned Z3 executable}"
command -v rustup >/dev/null || {
    echo "the matching rustup must be available on PATH" >&2
    exit 2
}

threads="${VERUS_THREADS:-2}"
temporary_root="${TMPDIR:-/tmp}"
output_dir="$(mktemp -d "$temporary_root/proveai-k3-runtime.XXXXXX")"
verus_library_dir="$(CDPATH= cd -- "$(dirname -- "$VERUS_BIN")" && pwd)"
rust_toolchain_bin="$(CDPATH= cd -- "$(dirname -- "$RUSTC")" && pwd)"
cargo_bin="${CARGO:-$rust_toolchain_bin/cargo}"
vstd_rlib="$verus_library_dir/libvstd.rlib"
verus_builtin_rlib="$verus_library_dir/libverus_builtin.rlib"
test -x "$cargo_bin"
test -f "$vstd_rlib"
test -f "$verus_builtin_rlib"
cleanup() {
    rm -rf -- "$output_dir"
}
trap cleanup EXIT

# Verus writes its proof-erased library beside the current working directory.
# Keeping that directory temporary prevents generated binaries from entering
# the source tree.
(
    cd "$output_dir"
    "$VERUS_BIN" "$repo_root/mechanized/k3_append_linearization_kernel.rs" \
        --crate-type lib --no-cheating --compile --num-threads "$threads"
)

rlib="$output_dir/libk3_append_linearization_kernel.rlib"
test -f "$rlib"
"$RUSTC" --edition=2021 "$repo_root/artifact/k3-runtime-harness.rs" \
    -L "dependency=$verus_library_dir" \
    --extern "k3_append_linearization_kernel=$rlib" \
    --extern "vstd=$vstd_rlib" \
    --extern "verus_builtin=$verus_builtin_rlib" \
    -o "$output_dir/k3-runtime-harness"
"$output_dir/k3-runtime-harness"

export RUSTC
export CARGO_TARGET_DIR="$output_dir/reference-broker-target"
"$cargo_bin" build --manifest-path "$repo_root/reference-broker/Cargo.toml" --lib
reference_broker_rlib="$(find "$CARGO_TARGET_DIR/debug/deps" -maxdepth 1 -type f \
    -name 'libproveai_reference_broker-*.rlib' -print -quit)"
test -n "$reference_broker_rlib"
reference_broker_dependency_dir="$(CDPATH= cd -- "$(dirname -- "$reference_broker_rlib")" && pwd)"
"$RUSTC" --edition=2021 "$repo_root/artifact/k3-m4-bridge-harness.rs" \
    -L "dependency=$verus_library_dir" \
    -L "dependency=$reference_broker_dependency_dir" \
    --extern "k3_append_linearization_kernel=$rlib" \
    --extern "proveai_reference_broker=$reference_broker_rlib" \
    --extern "vstd=$vstd_rlib" \
    --extern "verus_builtin=$verus_builtin_rlib" \
    -o "$output_dir/k3-m4-bridge-harness"
"$output_dir/k3-m4-bridge-harness"
