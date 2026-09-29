# Decision discrimination campaign

Run from the repository root with Rust 1.96.0 and Python 3:

    python3 reference-broker/evaluation/run_decision_discrimination.py --output reference-broker/evaluation/results/decision-discrimination.json

Use --cargo to select an explicit Cargo executable and RUSTC to select
its compiler. The crate has no external dependencies; Cargo runs offline.

The two assertion tests in tests/decision_discrimination.rs exercise four
scenarios. A third test is a child-process service entry point, not another
scenario. Every invocation launches that child, which either creates a
synced marker file or rejects without mutation. The oracle reads the file
directly; neither broker records nor the kernel provide its effect value.

The paired runs stop after Start (no invocation) and after invocation
(marker written, reply not retained). Recovery records Ambiguous for the
interrupted attempt, then the service rejects the retry. A second injected
interruption occurs after that Failure is retained. The test compares both
initial prefixes and both decision prefixes for exact equality. Both runs
end Unknown despite different service states. Mapping the final retained
Failure to Fail is unsafe in the one-effect run. Success and explicit
rejection controls demonstrate Commit/one and Fail/zero, preserved on reopen
without another call. This is a response-only decision-rule comparison,
not execution of a competing workflow system.

The runner additionally runs adapter_semantics and recovery_interruption.
The retained run has 11 passing Rust test functions including the service
entry point; it is not 11 independent discrimination scenarios. The JSON
retains stdout, stderr, toolchain, command, base revision, and SHA-256 values
of actual source files, so local changes are not concealed by a Git hash.

Scope: ungated Broker::open; separate local child process; injected broker
errors followed by reopen. There is no OS-kill, power-loss, network-service,
directory-durability, or deployed-API validation. The reference service is
purpose-built, not independently specified by a third-party service. This
run does not reverify any Verus/TLA+ target or refresh the 21-case gate report.
