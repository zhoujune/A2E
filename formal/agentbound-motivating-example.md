# Motivating Example: Authorized Write, Lost Reply

This example is the paper-facing design anchor for the comparison with
AgentBound. It is intentionally MCP-like rather than a claim about a specific
MCP implementation.

## Scenario

An agent asks a broker to append a generated record to
`/workspace/report.log` through a protected `append_report_entry` tool. The
user-approved resource policy permits writes to that path. An AgentBound-style
manifest and sandbox can therefore authorize the filesystem resource and
prevent access outside the declared scope. The request is legitimate with
respect to the resource policy, but executing it twice would append two
records.

For the Deduplicated version, the broker assigns request `r` and stable key
`k`, durably records authorization and invocation intent, and invokes the
service. The service atomically appends the record and memoizes the decision
for `k`, but the process crashes before the broker receives or persists the
result.

## Critical trace

| Prefix | Broker/journal event | Protected-service state | Knowledge available after crash |
|---|---|---|---|
| 0 | `Authorize(r, capability, scope)` | unchanged | authorization is durable |
| 1 | `Prepare(r)` | unchanged | request is bound to the tool |
| 2 | `Arm(r)` and `Start(r, attempt=1)` | unchanged | physical attempt is authorized |
| 3 | `Invoke(r, k)` | unchanged | call is in flight |
| 4 | service linearizes `append(k, entry)` | one log record appended; `k` memoized | effect happened, broker has no delivery |
| 5 | crash before `Deliver`/`PersistOutcome` | effect remains | durable broker state sees unresolved attempt |
| 6a | retry with `k` | service returns memoized success | `Deduplicated` resolves the ambiguity |
| 6b | blind retry without a service contract | a second append may occur | ProveAI's `Uncontrolled` policy forbids the retry and terminates `Unknown` |

## What each boundary establishes

An access-control sandbox answers the resource question: the tool may write
`/workspace/report.log`, but not `/etc/passwd` or an undeclared network host.
It does not, by itself, answer whether repeating a permitted write after the
crash duplicates an external effect or how the broker should classify the
outcome.

The ProveAI protocol makes the missing answer adapter-specific:

- `Idempotent`: a repeated operation refines one abstract mutation under the
  adapter's idempotence law;
- `Deduplicated`: the stable key `k` is service-owned durable evidence, so the
  retry returns the memoized success without a second mutation; and
- `Uncontrolled`: the broker cannot establish whether the first call took
  effect and records `Unknown` rather than claiming `Fail` or retrying blindly.

The formal closed-interface model then requires the protected mutation to be
coupled to a broker-mediated invocation with durable authorization ancestry.
An AgentBound-style sandbox is a plausible deployment mechanism for realizing
the resource and handle-exclusivity assumptions, but it does not replace the
crash-aware effect proof.

## Evaluation hook

The executable evaluation should implement this trace with a fault injected
between service linearization and broker delivery. The oracle must check:

1. exactly one terminal record for `r`;
2. authorization ancestry for every invocation;
3. one abstract effect for the `Idempotent` and `Deduplicated` contracts;
4. `Unknown` for the unresolved `Uncontrolled` contract; and
5. rejection of a stale or duplicate delivery after recovery.

This is a semantic stress case, not evidence that the reference Rust broker
refines a production filesystem or MCP server.
