# Linux artifact results

`linux-smoke-preflight.json` is a server-generated dry-run of the Linux TLA+
artifact runner.

- Source revision: `740f50069abe0219bfef9aa234d957d761a87a1b`
- Status: `dry_run` (no TLC process was claimed)
- Suite: smoke, 8 scenarios
- Isolated inputs: all 14 local TLA+ modules plus the selected smoke configurations
- SHA-256: `bd5d5b84dfda42f387a2fb6570e5324de78a91a4a4cafb8972e38a1bf61b83c5`

The runner and dependency-free validator both passed. An executed Linux run is
not implied by this preflight. A current executed full run is retained as
`tla-full-9a45d39.json`:

- Source revision: `9a45d391e8c19d3f069a3df271005b1fd6b39b60`
- Status: `passed`, suite: full, 13/13 scenarios
- 32 workers, 357232 ms, SHA-256:
  `114dab828acce4dcd8baa80e888128a23e5af8c486d4f33f9ba737a8e18700d5`

The run used the hash-locked Temurin and TLA+ Tools artifacts on the server.
The earlier `5d8e8ed` reports remain retained for historical clean-room
comparison.

`archive-smoke-preflight-7fc87a7.json` was generated from the unpacked
anonymous archive rather than a Git checkout. Its export-substituted source
revision is `7fc87a7b30cef0ce1de3ee5d098897e5ce5b90b1`; the TLA+ snapshot dry-run,
report validation, Rust formatting/tests, and post-run release scan passed.
Report SHA-256:
`01f1c45fd3b6f4d3b3cf6c7b0dbcc00fea2ec8f18819b9dc6251956ed791cd30`.
