# Linux artifact preflight

`linux-smoke-preflight.json` is a server-generated dry-run of the Linux TLA+
artifact runner.

- Source revision: `740f50069abe0219bfef9aa234d957d761a87a1b`
- Status: `dry_run` (no TLC process was claimed)
- Suite: smoke, 8 scenarios
- Isolated inputs: all 14 local TLA+ modules plus the selected smoke configurations
- SHA-256: `bd5d5b84dfda42f387a2fb6570e5324de78a91a4a4cafb8972e38a1bf61b83c5`

The runner and dependency-free validator both passed. An executed Linux run is
not retained yet: the server has no Java 21.0.11 or TLA+ Tools cache, and its
attempted upstream Adoptium/GitHub downloads reset the connection. The runner
therefore fails closed with a prerequisite error until a hash-pinned JRE or
container is supplied.
