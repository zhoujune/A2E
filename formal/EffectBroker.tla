---- MODULE EffectBroker ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, EffectBrokerParameters

(***************************************************************************
 * Executable safety model for the Verified Agent Effect Broker.           *
 *                                                                         *
 * externalHistory and the source indices into it are proof-only ghost state. *
 * Recovery decisions rely only on durable broker state.                      *
 ************************************************************************ ***)

CONSTANTS
    NoCap,
    NoResult

Phases == {
    "New", "Authorized", "Prepared", "Armed",
    "Committed", "Failed", "Unknown"
}

ExternalEventKinds == {
    "Invoke", "Success", "Failure", "Ambiguous", "InvalidResult"
}
OutcomeKinds == ExternalEventKinds \ {"Invoke"}
AttemptEventKinds == {
    "Started", "Success", "Failure", "Ambiguous", "InvalidResult"
}

ASSUME
    /\ CommonParametersOK
    /\ NoCap \notin Caps
    /\ NoResult \notin Results

VARIABLES
    phase,
    capRemaining,
    revoked,
    authWitness,
    authCount,
    authLog,
    attemptLog,
    externalHistory,
    commitCount,
    commitLog,
    committedValue,
    commitSource,
    commitAttempt,
    failureAttempt,
    ready,
    readyAttempt,
    inflight,
    inflightAttempt,
    received,
    receivedKind,
    receivedValue,
    receivedSource,
    receivedAttempt,
    observedOK,
    observedValue,
    observedSource,
    observedAttempt,
    observedErr,
    observedErrSource,
    observedErrAttempt,
    observedUnknown,
    crashed,
    recovering

vars == <<
    phase, capRemaining, revoked, authWitness, authCount, authLog,
    attemptLog, externalHistory, commitCount, commitLog, committedValue,
    commitSource, commitAttempt, failureAttempt, ready, readyAttempt, inflight,
    inflightAttempt, received, receivedKind, receivedValue, receivedSource,
    receivedAttempt, observedOK, observedValue, observedSource,
    observedAttempt, observedErr, observedErrSource, observedErrAttempt,
    observedUnknown, crashed, recovering
>>

Matching(r, c) ==
    /\ c = RequestCap(r)
    /\ r \in BaseScopeMatched
    /\ r \in ResourceScopeMatched
    /\ r \in ArgumentConstraintMatched

RetryClass(r) ==
    CASE r \in ReadOnlyRequests -> "ReadOnly"
    [] r \in IdempotentRequests -> "Idempotent"
    [] r \in DeduplicatedRequests -> "Deduplicated"
    [] OTHER -> "Uncontrolled"

ValidCap(r, c) ==
    /\ RequestCap(r) = c
    /\ Matching(r, c)
    /\ c \notin revoked
    /\ capRemaining[c] > 0

SeqRange(s) == {s[i] : i \in 1..Len(s)}

NoDuplicates(s) ==
    \A i, j \in 1..Len(s) : s[i] = s[j] => i = j

AuthRequests(s) ==
    [i \in 1..Len(s) |-> s[i][1]]

ExternalEvent(r, attempt, kind, value) == <<r, attempt, kind, value>>

ExternalEventUniverse ==
    {ExternalEvent(r, attempt, kind, value) :
        r \in Requests,
        attempt \in 1..MaxAttempts,
        kind \in ExternalEventKinds,
        value \in Results \union {NoResult}}

AttemptRecord(r, attempt, kind) == <<r, attempt, kind>>

AttemptRecordUniverse ==
    {AttemptRecord(r, attempt, kind) :
        r \in Requests,
        attempt \in 1..MaxAttempts,
        kind \in AttemptEventKinds}

CommitEntry(r, value) == <<r, value>>

CommitRequests(s) ==
    [i \in 1..Len(s) |-> s[i][1]]

HistoryCount(r, kind) ==
    Cardinality({i \in 1..Len(externalHistory) :
        /\ externalHistory[i][1] = r
        /\ externalHistory[i][3] = kind})

HistoryAttemptCount(r, attempt, kind) ==
    Cardinality({i \in 1..Len(externalHistory) :
        /\ externalHistory[i][1] = r
        /\ externalHistory[i][2] = attempt
        /\ externalHistory[i][3] = kind})

SuccessIndices(r) ==
    {i \in 1..Len(externalHistory) :
        /\ externalHistory[i][1] = r
        /\ externalHistory[i][3] = "Success"}

SuccessfulValues(r) ==
    {externalHistory[i][4] : i \in SuccessIndices(r)}

InvalidResultIndices(r) ==
    {i \in 1..Len(externalHistory) :
        /\ externalHistory[i][1] = r
        /\ externalHistory[i][3] = "InvalidResult"}

InvalidResultValues(r) ==
    {externalHistory[i][4] : i \in InvalidResultIndices(r)}

InvocationCount(r) == HistoryCount(r, "Invoke")

OutcomeCount(r) ==
    HistoryCount(r, "Success")
    + HistoryCount(r, "Failure")
    + HistoryCount(r, "Ambiguous")
    + HistoryCount(r, "InvalidResult")

HasHistoryEvent(r, kind) == HistoryCount(r, kind) > 0

HasUnresolvedInvocation(r) == OutcomeCount(r) < InvocationCount(r)

HasUncertainOutcome(r) ==
    HasUnresolvedInvocation(r)
    \/ HasHistoryEvent(r, "Ambiguous")
    \/ HasHistoryEvent(r, "InvalidResult")

AttemptLogCount(r, kind) ==
    Cardinality({i \in 1..Len(attemptLog) :
        /\ attemptLog[i][1] = r
        /\ attemptLog[i][3] = kind})

AttemptLogEntryCount(r, attempt, kind) ==
    Cardinality({i \in 1..Len(attemptLog) :
        attemptLog[i] = AttemptRecord(r, attempt, kind)})

DurableAttemptCount(r) == AttemptLogCount(r, "Started")

DurableOutcomeCount(r) ==
    AttemptLogCount(r, "Success")
    + AttemptLogCount(r, "Failure")
    + AttemptLogCount(r, "Ambiguous")
    + AttemptLogCount(r, "InvalidResult")

HasDurableAttemptEvent(r, kind) == AttemptLogCount(r, kind) > 0

HasUnresolvedDurableAttempt(r) ==
    DurableOutcomeCount(r) < DurableAttemptCount(r)

HasDurableUncertainty(r) ==
    HasUnresolvedDurableAttempt(r)
    \/ HasDurableAttemptEvent(r, "Success")
    \/ HasDurableAttemptEvent(r, "Ambiguous")
    \/ HasDurableAttemptEvent(r, "InvalidResult")

AllDurableAttemptsFailed(r) ==
    /\ DurableAttemptCount(r) > 0
    /\ DurableAttemptCount(r) = AttemptLogCount(r, "Failure")

(***************************************************************************
 * These predicates are adapter-environment assumptions. They restrict which *
 * observations a declared deduplicated service may produce; the broker does *
 * not inspect ghost history to make retry or recovery decisions.              *
 ************************************************************************ ***)

AdapterAllowsSuccess(r, value) ==
    RetryClass(r) = "Deduplicated" =>
        /\ ~HasHistoryEvent(r, "Failure")
        /\ ~HasHistoryEvent(r, "InvalidResult")
        /\ (SuccessfulValues(r) = {} \/ value \in SuccessfulValues(r))

AdapterAllowsFailure(r) ==
    RetryClass(r) = "Deduplicated" =>
        /\ ~HasHistoryEvent(r, "Success")
        /\ ~HasHistoryEvent(r, "InvalidResult")

AdapterAllowsInvalidResult(r, value) ==
    RetryClass(r) = "Deduplicated" =>
        /\ ~HasHistoryEvent(r, "Success")
        /\ ~HasHistoryEvent(r, "Failure")
        /\ (InvalidResultValues(r) = {} \/
            value \in InvalidResultValues(r))

LatestAttemptFailed(r) ==
    /\ DurableAttemptCount(r) > 0
    /\ AttemptLogEntryCount(
           r, DurableAttemptCount(r), "Failure") = 1

FailureIsConclusive(r) ==
    /\ LatestAttemptFailed(r)
        /\ (RetryClass(r) = "Idempotent" => AllDurableAttemptsFailed(r))

EvidenceDecision(r) ==
    IF phase[r] # "Armed" THEN "Stable"
    ELSE IF HasDurableAttemptEvent(r, "Success") THEN "Commit"
    ELSE IF FailureIsConclusive(r) THEN "Fail"
    ELSE IF LatestAttemptFailed(r) THEN "Unknown"
    ELSE IF DurableAttemptCount(r) < MaxAttempts
            /\ (DurableAttemptCount(r) = 0
                \/ RetryClass(r) # "Uncontrolled")
         THEN "Retry"
    ELSE "Unknown"

UnsafeUncontrolled(r) ==
    /\ phase[r] = "Armed"
    /\ RetryClass(r) = "Uncontrolled"
    /\ ~FailureIsConclusive(r)

RecoveryComplete ==
    \A r \in Requests :
        phase[r] # "Armed" \/ EvidenceDecision(r) = "Retry"

Running == ~crashed /\ ~recovering

PossibleEffectCounts(r) ==
    CASE RetryClass(r) = "ReadOnly" -> {0}
    [] RetryClass(r) = "Deduplicated" ->
           IF HasHistoryEvent(r, "Success") THEN {1}
           ELSE IF HasHistoryEvent(r, "Failure") THEN {0}
           ELSE IF HasUncertainOutcome(r) THEN {0, 1}
           ELSE {0}
    [] RetryClass(r) = "Idempotent" ->
           IF HasHistoryEvent(r, "Success") THEN {1}
           ELSE IF HasUncertainOutcome(r) THEN {0, 1}
           ELSE {0}
    [] OTHER ->
           IF HasHistoryEvent(r, "Success") THEN {1}
           ELSE IF HasHistoryEvent(r, "Failure") THEN {0}
           ELSE IF HasUncertainOutcome(r) THEN {0, 1}
           ELSE {0}

Init ==
    /\ phase = [r \in Requests |-> "New"]
    /\ capRemaining = [c \in Caps |-> InitialBudget(c)]
    /\ revoked = {}
    /\ authWitness = [r \in Requests |-> NoCap]
    /\ authCount = [c \in Caps |-> 0]
    /\ authLog = <<>>
    /\ attemptLog = <<>>
    /\ externalHistory = <<>>
    /\ commitCount = [r \in Requests |-> 0]
    /\ commitLog = <<>>
    /\ committedValue = [r \in Requests |-> NoResult]
    /\ commitSource = [r \in Requests |-> 0]
    /\ commitAttempt = [r \in Requests |-> 0]
    /\ failureAttempt = [r \in Requests |-> 0]
    /\ ready = {}
    /\ readyAttempt = [r \in Requests |-> 0]
    /\ inflight = {}
    /\ inflightAttempt = [r \in Requests |-> 0]
    /\ received = {}
    /\ receivedKind = [r \in Requests |-> "None"]
    /\ receivedValue = [r \in Requests |-> NoResult]
    /\ receivedSource = [r \in Requests |-> 0]
    /\ receivedAttempt = [r \in Requests |-> 0]
    /\ observedOK = {}
    /\ observedValue = [r \in Requests |-> NoResult]
    /\ observedSource = [r \in Requests |-> 0]
    /\ observedAttempt = [r \in Requests |-> 0]
    /\ observedErr = {}
    /\ observedErrSource = [r \in Requests |-> 0]
    /\ observedErrAttempt = [r \in Requests |-> 0]
    /\ observedUnknown = {}
    /\ crashed = FALSE
    /\ recovering = FALSE

Authorize(r) ==
    LET c == RequestCap(r) IN
    /\ Running
    /\ phase[r] = "New"
    /\ ValidCap(r, c)
    /\ phase' = [phase EXCEPT ![r] = "Authorized"]
    /\ capRemaining' = [capRemaining EXCEPT ![c] = @ - 1]
    /\ authWitness' = [authWitness EXCEPT ![r] = c]
    /\ authCount' = [authCount EXCEPT ![c] = @ + 1]
    /\ authLog' = Append(authLog, <<r, c>>)
    /\ UNCHANGED <<
           revoked, attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt, ready,
           readyAttempt, inflight, inflightAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue, observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

Revoke(c) ==
    /\ Running
    /\ c \in Caps \ revoked
    /\ revoked' = revoked \union {c}
    /\ UNCHANGED <<
           phase, capRemaining, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt, ready,
           readyAttempt, inflight, inflightAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue, observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

Prepare(r) ==
    /\ Running
    /\ phase[r] = "Authorized"
    /\ phase' = [phase EXCEPT ![r] = "Prepared"]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt, ready,
           readyAttempt, inflight, inflightAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue, observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

Arm(r) ==
    /\ Running
    /\ phase[r] = "Prepared"
    /\ phase' = [phase EXCEPT ![r] = "Armed"]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt, ready,
           readyAttempt, inflight, inflightAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue, observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

ReserveAttempt(r) ==
    LET attempt == DurableAttemptCount(r) + 1 IN
    /\ Running
    /\ phase[r] = "Armed"
    /\ authWitness[r] # NoCap
    /\ r \notin ready \union inflight \union received
                  \union observedOK \union observedErr
                  \union observedUnknown
    /\ DurableAttemptCount(r) < MaxAttempts
    /\ EvidenceDecision(r) = "Retry"
    /\ (RetryClass(r) = "Uncontrolled" => DurableAttemptCount(r) = 0)
    /\ ready' = ready \union {r}
    /\ readyAttempt' = [readyAttempt EXCEPT ![r] = attempt]
    /\ attemptLog' = Append(
           attemptLog, AttemptRecord(r, attempt, "Started"))
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount,
           authLog, externalHistory, commitCount, commitLog, committedValue,
           commitSource, commitAttempt, failureAttempt, inflight,
           inflightAttempt, received, receivedKind, receivedValue,
           receivedSource, receivedAttempt, observedOK, observedValue,
           observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

SendAttempt(r, attempt) ==
    /\ Running
    /\ r \in ready
    /\ attempt \in 1..MaxAttempts
    /\ attempt = readyAttempt[r]
    /\ ready' = ready \ {r}
    /\ readyAttempt' = [readyAttempt EXCEPT ![r] = 0]
    /\ inflight' = inflight \union {r}
    /\ inflightAttempt' = [inflightAttempt EXCEPT ![r] = attempt]
    /\ externalHistory' = Append(
           externalHistory, ExternalEvent(r, attempt, "Invoke", NoResult))
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, commitCount, commitLog, committedValue, commitSource,
           commitAttempt, failureAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue,
           observedSource, observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

DeliverOK(r, attempt, value) ==
    /\ Running
    /\ r \in inflight
    /\ attempt \in 1..MaxAttempts
    /\ attempt = inflightAttempt[r]
    /\ value \in AllowedResults
    /\ AdapterAllowsSuccess(r, value)
    /\ inflight' = inflight \ {r}
    /\ inflightAttempt' = [inflightAttempt EXCEPT ![r] = 0]
    /\ received' = received \union {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "Success"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = value]
    /\ receivedSource' =
           [receivedSource EXCEPT ![r] = Len(externalHistory) + 1]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = attempt]
    /\ externalHistory' = Append(
           externalHistory, ExternalEvent(r, attempt, "Success", value))
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount,
           authLog, attemptLog, commitCount, commitLog, committedValue,
           commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
           observedOK, observedValue, observedSource, observedAttempt,
           observedErr, observedErrSource, observedErrAttempt,
           observedUnknown, crashed, recovering
       >>

PersistOK(r) ==
    /\ Running
    /\ r \in received
    /\ receivedKind[r] = "Success"
    /\ receivedAttempt[r] \in 1..MaxAttempts
    /\ receivedValue[r] \in AllowedResults
    /\ received' = received \ {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "None"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = NoResult]
    /\ receivedSource' = [receivedSource EXCEPT ![r] = 0]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = 0]
    /\ attemptLog' = Append(
           attemptLog,
           AttemptRecord(r, receivedAttempt[r], "Success"))
    /\ observedOK' = observedOK \union {r}
    /\ observedValue' = [observedValue EXCEPT ![r] = receivedValue[r]]
    /\ observedSource' = [observedSource EXCEPT ![r] = receivedSource[r]]
    /\ observedAttempt' =
           [observedAttempt EXCEPT ![r] = receivedAttempt[r]]
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           externalHistory, commitCount, commitLog, committedValue,
           commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
           inflight, inflightAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

DeliverErr(r, attempt) ==
    /\ Running
    /\ r \in inflight
    /\ attempt \in 1..MaxAttempts
    /\ attempt = inflightAttempt[r]
    /\ AdapterAllowsFailure(r)
    /\ inflight' = inflight \ {r}
    /\ inflightAttempt' = [inflightAttempt EXCEPT ![r] = 0]
    /\ received' = received \union {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "Failure"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = NoResult]
    /\ receivedSource' =
           [receivedSource EXCEPT ![r] = Len(externalHistory) + 1]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = attempt]
    /\ externalHistory' = Append(
           externalHistory, ExternalEvent(r, attempt, "Failure", NoResult))
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount,
           authLog, attemptLog, commitCount, commitLog, committedValue,
           commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
           observedOK, observedValue, observedSource, observedAttempt,
           observedErr, observedErrSource, observedErrAttempt,
           observedUnknown, crashed, recovering
       >>

PersistErr(r) ==
    /\ Running
    /\ r \in received
    /\ receivedKind[r] = "Failure"
    /\ receivedAttempt[r] \in 1..MaxAttempts
    /\ received' = received \ {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "None"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = NoResult]
    /\ receivedSource' = [receivedSource EXCEPT ![r] = 0]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = 0]
    /\ attemptLog' = Append(
           attemptLog,
           AttemptRecord(r, receivedAttempt[r], "Failure"))
    /\ observedErr' = observedErr \union {r}
    /\ observedErrSource' =
           [observedErrSource EXCEPT ![r] = receivedSource[r]]
    /\ observedErrAttempt' =
           [observedErrAttempt EXCEPT ![r] = receivedAttempt[r]]
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           externalHistory, commitCount, commitLog, committedValue,
           commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
           inflight, inflightAttempt, observedOK, observedValue,
           observedSource, observedAttempt, observedUnknown, crashed,
           recovering
       >>

DeliverAmbiguous(r, attempt) ==
    /\ Running
    /\ r \in inflight
    /\ attempt \in 1..MaxAttempts
    /\ attempt = inflightAttempt[r]
    /\ inflight' = inflight \ {r}
    /\ inflightAttempt' = [inflightAttempt EXCEPT ![r] = 0]
    /\ received' = received \union {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "Ambiguous"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = NoResult]
    /\ receivedSource' =
           [receivedSource EXCEPT ![r] = Len(externalHistory) + 1]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = attempt]
    /\ externalHistory' = Append(
           externalHistory, ExternalEvent(r, attempt, "Ambiguous", NoResult))
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, commitCount, commitLog, committedValue, commitSource,
           commitAttempt, failureAttempt, ready, readyAttempt, observedOK,
           observedValue, observedSource, observedAttempt, observedErr,
           observedErrSource, observedErrAttempt, observedUnknown, crashed,
           recovering
       >>

PersistAmbiguous(r) ==
    /\ Running
    /\ r \in received
    /\ receivedKind[r] = "Ambiguous"
    /\ receivedAttempt[r] \in 1..MaxAttempts
    /\ received' = received \ {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "None"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = NoResult]
    /\ receivedSource' = [receivedSource EXCEPT ![r] = 0]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = 0]
    /\ attemptLog' = Append(
           attemptLog,
           AttemptRecord(r, receivedAttempt[r], "Ambiguous"))
    /\ observedUnknown' =
           IF RetryClass(r) = "Uncontrolled"
           THEN observedUnknown \union {r}
           ELSE observedUnknown
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           externalHistory, commitCount, commitLog, committedValue,
           commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
           inflight, inflightAttempt, observedOK, observedValue,
           observedSource, observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, crashed, recovering
       >>

DeliverInvalidResult(r, attempt, value) ==
    /\ Running
    /\ r \in inflight
    /\ attempt \in 1..MaxAttempts
    /\ attempt = inflightAttempt[r]
    /\ value \in Results \ AllowedResults
    /\ AdapterAllowsInvalidResult(r, value)
    /\ inflight' = inflight \ {r}
    /\ inflightAttempt' = [inflightAttempt EXCEPT ![r] = 0]
    /\ received' = received \union {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "InvalidResult"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = value]
    /\ receivedSource' =
           [receivedSource EXCEPT ![r] = Len(externalHistory) + 1]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = attempt]
    /\ externalHistory' = Append(
           externalHistory,
           ExternalEvent(r, attempt, "InvalidResult", value))
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, commitCount, commitLog, committedValue, commitSource,
           commitAttempt, failureAttempt, ready, readyAttempt, observedOK,
           observedValue, observedSource, observedAttempt, observedErr,
           observedErrSource, observedErrAttempt, observedUnknown, crashed,
           recovering
       >>

PersistInvalidResult(r) ==
    /\ Running
    /\ r \in received
    /\ receivedKind[r] = "InvalidResult"
    /\ receivedAttempt[r] \in 1..MaxAttempts
    /\ receivedValue[r] \in Results \ AllowedResults
    /\ received' = received \ {r}
    /\ receivedKind' = [receivedKind EXCEPT ![r] = "None"]
    /\ receivedValue' = [receivedValue EXCEPT ![r] = NoResult]
    /\ receivedSource' = [receivedSource EXCEPT ![r] = 0]
    /\ receivedAttempt' = [receivedAttempt EXCEPT ![r] = 0]
    /\ attemptLog' = Append(
           attemptLog,
           AttemptRecord(r, receivedAttempt[r], "InvalidResult"))
    /\ observedUnknown' =
           IF RetryClass(r) = "Uncontrolled"
           THEN observedUnknown \union {r}
           ELSE observedUnknown
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           externalHistory, commitCount, commitLog, committedValue,
           commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
           inflight, inflightAttempt, observedOK, observedValue,
           observedSource, observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, crashed, recovering
       >>

RecordObservedUnknown(r) ==
    /\ Running
    /\ phase[r] = "Armed"
    /\ r \in observedUnknown
    /\ RetryClass(r) = "Uncontrolled"
    /\ EvidenceDecision(r) = "Unknown"
    /\ AttemptLogEntryCount(
           r, DurableAttemptCount(r), "Ambiguous")
       + AttemptLogEntryCount(
           r, DurableAttemptCount(r), "InvalidResult") = 1
    /\ phase' = [phase EXCEPT ![r] = "Unknown"]
    /\ observedUnknown' = observedUnknown \ {r}
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt,
           ready, readyAttempt, inflight, inflightAttempt, received,
           receivedKind, receivedValue, receivedSource, receivedAttempt,
           observedOK, observedValue, observedSource, observedAttempt,
           observedErr, observedErrSource, observedErrAttempt, crashed,
           recovering
       >>

Commit(r) ==
    /\ Running
    /\ phase[r] = "Armed"
    /\ r \in observedOK
    /\ EvidenceDecision(r) = "Commit"
    /\ observedValue[r] \in AllowedResults
    /\ observedAttempt[r] \in 1..MaxAttempts
    /\ commitCount[r] = 0
    /\ phase' = [phase EXCEPT ![r] = "Committed"]
    /\ commitCount' = [commitCount EXCEPT ![r] = 1]
    /\ commitLog' = Append(
           commitLog, CommitEntry(r, observedValue[r]))
    /\ committedValue' =
           [committedValue EXCEPT ![r] = observedValue[r]]
    /\ commitSource' =
           [commitSource EXCEPT ![r] = observedSource[r]]
    /\ commitAttempt' =
           [commitAttempt EXCEPT ![r] = observedAttempt[r]]
    /\ observedOK' = observedOK \ {r}
    /\ observedValue' = [observedValue EXCEPT ![r] = NoResult]
    /\ observedSource' = [observedSource EXCEPT ![r] = 0]
    /\ observedAttempt' = [observedAttempt EXCEPT ![r] = 0]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, ready, readyAttempt, inflight,
           inflightAttempt, received, receivedKind, receivedValue,
           receivedSource, receivedAttempt, failureAttempt, observedErr,
           observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

RecordFailure(r) ==
    /\ Running
    /\ phase[r] = "Armed"
    /\ r \in observedErr
    /\ FailureIsConclusive(r)
    /\ EvidenceDecision(r) = "Fail"
    /\ observedErrAttempt[r] = DurableAttemptCount(r)
    /\ phase' = [phase EXCEPT ![r] = "Failed"]
    /\ failureAttempt' =
           [failureAttempt EXCEPT ![r] = observedErrAttempt[r]]
    /\ observedErr' = observedErr \ {r}
    /\ observedErrSource' = [observedErrSource EXCEPT ![r] = 0]
    /\ observedErrAttempt' = [observedErrAttempt EXCEPT ![r] = 0]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, ready, readyAttempt,
           inflight, inflightAttempt, received, receivedKind, receivedValue,
           receivedSource, receivedAttempt, observedOK, observedValue,
           observedSource,
           observedAttempt, observedUnknown, crashed, recovering
       >>

RecordUnknown(r) ==
    /\ Running
    /\ phase[r] = "Armed"
    /\ r \in observedErr
    /\ ~FailureIsConclusive(r)
    /\ EvidenceDecision(r) = "Unknown"
    /\ phase' = [phase EXCEPT ![r] = "Unknown"]
    /\ observedErr' = observedErr \ {r}
    /\ observedErrSource' = [observedErrSource EXCEPT ![r] = 0]
    /\ observedErrAttempt' = [observedErrAttempt EXCEPT ![r] = 0]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt, ready,
           readyAttempt, inflight, inflightAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue, observedSource,
           observedAttempt, observedUnknown, crashed, recovering
       >>

RetryAfterUncertainFailure(r) ==
    /\ Running
    /\ phase[r] = "Armed"
    /\ RetryClass(r) = "Idempotent"
    /\ r \in observedErr
    /\ ~FailureIsConclusive(r)
    /\ DurableAttemptCount(r) < MaxAttempts
    /\ observedErr' = observedErr \ {r}
    /\ observedErrSource' = [observedErrSource EXCEPT ![r] = 0]
    /\ observedErrAttempt' = [observedErrAttempt EXCEPT ![r] = 0]
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt,
           ready, readyAttempt, inflight, inflightAttempt, received,
           receivedKind, receivedValue, receivedSource, receivedAttempt,
           observedOK, observedValue, observedSource, observedAttempt,
           observedUnknown, crashed, recovering
       >>

RecoverRecordedFailure(r) ==
    /\ recovering
    /\ phase[r] = "Armed"
    /\ r \notin ready \union inflight \union received
                  \union observedOK \union observedErr
                  \union observedUnknown
    /\ FailureIsConclusive(r)
    /\ EvidenceDecision(r) = "Fail"
    /\ phase' = [phase EXCEPT ![r] = "Failed"]
    /\ failureAttempt' =
           [failureAttempt EXCEPT ![r] = DurableAttemptCount(r)]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, ready, readyAttempt,
           inflight, inflightAttempt, received, receivedKind, receivedValue,
           receivedSource, receivedAttempt, observedOK, observedValue,
           observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

ExhaustedUnknown(r) ==
    /\ Running
    /\ phase[r] = "Armed"
    /\ r \notin ready \union inflight \union received
                  \union observedOK \union observedErr
                  \union observedUnknown
    /\ DurableAttemptCount(r) = MaxAttempts
    /\ HasDurableUncertainty(r)
    /\ EvidenceDecision(r) = "Unknown"
    /\ phase' = [phase EXCEPT ![r] = "Unknown"]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt, ready,
           readyAttempt, inflight, inflightAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue, observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown, crashed, recovering
       >>

Crash ==
    /\ ~crashed
    /\ crashed' = TRUE
    /\ recovering' = FALSE
    /\ ready' = {}
    /\ readyAttempt' = [r \in Requests |-> 0]
    /\ inflight' = {}
    /\ inflightAttempt' = [r \in Requests |-> 0]
    /\ received' = {}
    /\ receivedKind' = [r \in Requests |-> "None"]
    /\ receivedValue' = [r \in Requests |-> NoResult]
    /\ receivedSource' = [r \in Requests |-> 0]
    /\ receivedAttempt' = [r \in Requests |-> 0]
    /\ observedOK' = {}
    /\ observedValue' = [r \in Requests |-> NoResult]
    /\ observedSource' = [r \in Requests |-> 0]
    /\ observedAttempt' = [r \in Requests |-> 0]
    /\ observedErr' = {}
    /\ observedErrSource' = [r \in Requests |-> 0]
    /\ observedErrAttempt' = [r \in Requests |-> 0]
    /\ observedUnknown' = {}
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount,
           authLog, attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt
       >>

BeginRecover ==
    /\ crashed
    /\ crashed' = FALSE
    /\ recovering' = TRUE
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt, ready,
           readyAttempt, inflight, inflightAttempt, received, receivedKind,
           receivedValue, receivedSource, receivedAttempt, observedOK,
           observedValue, observedSource,
           observedAttempt, observedErr, observedErrSource,
           observedErrAttempt, observedUnknown
       >>

QuarantineUncontrolled(r) ==
    /\ recovering
    /\ UnsafeUncontrolled(r)
    /\ phase' = [phase EXCEPT ![r] = "Unknown"]
    /\ UNCHANGED <<
           capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt,
           ready, readyAttempt, inflight, inflightAttempt, received,
           receivedKind, receivedValue, receivedSource, receivedAttempt,
           observedOK, observedValue, observedSource, observedAttempt, observedErr,
           observedErrSource, observedErrAttempt, observedUnknown, crashed,
           recovering
       >>

FinishRecover ==
    /\ recovering
    /\ RecoveryComplete
    /\ recovering' = FALSE
    /\ UNCHANGED <<
           phase, capRemaining, revoked, authWitness, authCount, authLog,
           attemptLog, externalHistory, commitCount, commitLog,
           committedValue, commitSource, commitAttempt, failureAttempt,
           ready, readyAttempt, inflight, inflightAttempt, received,
           receivedKind, receivedValue, receivedSource, receivedAttempt,
           observedOK, observedValue, observedSource, observedAttempt, observedErr,
           observedErrSource, observedErrAttempt, observedUnknown, crashed
       >>

Next ==
    \/ \E r \in Requests : Authorize(r)
    \/ \E c \in Caps : Revoke(c)
    \/ \E r \in Requests : Prepare(r)
    \/ \E r \in Requests : Arm(r)
    \/ \E r \in Requests : ReserveAttempt(r)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts :
           SendAttempt(r, attempt)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts,
          value \in AllowedResults : DeliverOK(r, attempt, value)
    \/ \E r \in Requests : PersistOK(r)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts :
           DeliverErr(r, attempt)
    \/ \E r \in Requests : PersistErr(r)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts :
           DeliverAmbiguous(r, attempt)
    \/ \E r \in Requests : PersistAmbiguous(r)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts,
          value \in Results \ AllowedResults :
           DeliverInvalidResult(r, attempt, value)
    \/ \E r \in Requests : PersistInvalidResult(r)
    \/ \E r \in Requests : RecordObservedUnknown(r)
    \/ \E r \in Requests : Commit(r)
    \/ \E r \in Requests : RecordFailure(r)
    \/ \E r \in Requests : RecordUnknown(r)
    \/ \E r \in Requests : RecoverRecordedFailure(r)
    \/ \E r \in Requests : ExhaustedUnknown(r)
    \/ Crash
    \/ BeginRecover
    \/ \E r \in Requests : QuarantineUncontrolled(r)
    \/ FinishRecover

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ phase \in [Requests -> Phases]
    /\ capRemaining \in [Caps -> Nat]
    /\ revoked \subseteq Caps
    /\ authWitness \in [Requests -> Caps \union {NoCap}]
    /\ authCount \in [Caps -> Nat]
    /\ authLog \in Seq(Requests \X Caps)
    /\ attemptLog \in Seq(AttemptRecordUniverse)
    /\ externalHistory \in Seq(ExternalEventUniverse)
    /\ commitCount \in [Requests -> 0..1]
    /\ commitLog \in Seq(Requests \X Results)
    /\ committedValue \in [Requests -> Results \union {NoResult}]
    /\ commitSource \in [Requests -> Nat]
    /\ commitAttempt \in [Requests -> Nat]
    /\ failureAttempt \in [Requests -> Nat]
    /\ ready \subseteq Requests
    /\ readyAttempt \in [Requests -> Nat]
    /\ inflight \subseteq Requests
    /\ inflightAttempt \in [Requests -> Nat]
    /\ received \subseteq Requests
    /\ receivedKind \in [Requests -> OutcomeKinds \union {"None"}]
    /\ receivedValue \in [Requests -> Results \union {NoResult}]
    /\ receivedSource \in [Requests -> Nat]
    /\ receivedAttempt \in [Requests -> Nat]
    /\ observedOK \subseteq Requests
    /\ observedValue \in [Requests -> Results \union {NoResult}]
    /\ observedSource \in [Requests -> Nat]
    /\ observedAttempt \in [Requests -> Nat]
    /\ observedErr \subseteq Requests
    /\ observedErrSource \in [Requests -> Nat]
    /\ observedErrAttempt \in [Requests -> Nat]
    /\ observedUnknown \subseteq Requests
    /\ crashed \in BOOLEAN
    /\ recovering \in BOOLEAN

CapabilityBudget ==
    \A c \in Caps :
        authCount[c] + capRemaining[c] = InitialBudget(c)

WitnessSound ==
    \A r \in Requests :
        authWitness[r] # NoCap => Matching(r, authWitness[r])

AuthLogSound ==
    /\ NoDuplicates(AuthRequests(authLog))
    /\ \A i \in 1..Len(authLog) :
           authWitness[authLog[i][1]] = authLog[i][2]
    /\ \A r \in Requests :
           (authWitness[r] # NoCap) <=>
               \E i \in 1..Len(authLog) :
                   /\ authLog[i][1] = r
                   /\ authLog[i][2] = authWitness[r]
    /\ \A c \in Caps :
           authCount[c] = Cardinality(
               {i \in 1..Len(authLog) : authLog[i][2] = c})

InvocationsAuthorized ==
    \A i \in 1..Len(externalHistory) :
        externalHistory[i][3] = "Invoke" =>
            LET r == externalHistory[i][1] IN
                /\ authWitness[r] # NoCap
                /\ Matching(r, authWitness[r])

ExternalHistoryWellFormed ==
    /\ \A r \in Requests, attempt \in 1..MaxAttempts :
           /\ HistoryAttemptCount(r, attempt, "Invoke") <= 1
           /\ HistoryAttemptCount(r, attempt, "Success")
              + HistoryAttemptCount(r, attempt, "Failure")
              + HistoryAttemptCount(r, attempt, "Ambiguous")
              + HistoryAttemptCount(r, attempt, "InvalidResult")
                  <= HistoryAttemptCount(r, attempt, "Invoke")
    /\ \A i \in 1..Len(externalHistory) :
           externalHistory[i][3] # "Invoke" =>
               \E j \in 1..(i - 1) :
                   externalHistory[j] =
                       ExternalEvent(
                           externalHistory[i][1],
                           externalHistory[i][2],
                           "Invoke",
                           NoResult)
    /\ \A i, j \in 1..Len(externalHistory) :
           ( /\ i < j
             /\ externalHistory[i][1] = externalHistory[j][1]
             /\ externalHistory[i][3] = "Invoke"
             /\ externalHistory[j][3] = "Invoke" ) =>
               externalHistory[i][2] < externalHistory[j][2]
    /\ \A i \in 1..Len(externalHistory) :
           externalHistory[i][3] # "Invoke" =>
               \A j \in 1..(i - 1) :
                   ( /\ externalHistory[j][1] = externalHistory[i][1]
                     /\ externalHistory[j][3] = "Invoke" ) =>
                       externalHistory[j][2] <= externalHistory[i][2]

AttemptLogWellFormed ==
    /\ \A r \in Requests : DurableAttemptCount(r) <= MaxAttempts
    /\ \A r \in Requests, attempt \in 1..MaxAttempts :
           /\ AttemptLogEntryCount(r, attempt, "Started") <= 1
           /\ AttemptLogEntryCount(r, attempt, "Success")
              + AttemptLogEntryCount(r, attempt, "Failure")
              + AttemptLogEntryCount(r, attempt, "Ambiguous")
              + AttemptLogEntryCount(r, attempt, "InvalidResult")
                  <= AttemptLogEntryCount(r, attempt, "Started")
    /\ \A r \in Requests :
           \A attempt \in 1..DurableAttemptCount(r) :
               AttemptLogEntryCount(r, attempt, "Started") = 1
    /\ \A i \in 1..Len(attemptLog) :
           attemptLog[i][3] # "Started" =>
               \E j \in 1..(i - 1) :
                   attemptLog[j] = AttemptRecord(
                       attemptLog[i][1], attemptLog[i][2], "Started")
    /\ \A i, j \in 1..Len(attemptLog) :
           ( /\ i < j
             /\ attemptLog[i][1] = attemptLog[j][1]
             /\ attemptLog[i][3] = "Started"
             /\ attemptLog[j][3] = "Started" ) =>
               attemptLog[i][2] < attemptLog[j][2]
    /\ \A i \in 1..Len(attemptLog) :
           attemptLog[i][3] # "Started" =>
               \A j \in 1..(i - 1) :
                   ( /\ attemptLog[j][1] = attemptLog[i][1]
                     /\ attemptLog[j][3] = "Started" ) =>
                       attemptLog[j][2] <= attemptLog[i][2]

AttemptLogBackedByHistory ==
    \A r \in Requests, attempt \in 1..MaxAttempts :
        /\ HistoryAttemptCount(r, attempt, "Invoke")
             <= AttemptLogEntryCount(r, attempt, "Started")
        /\ \A kind \in {"Success", "Failure", "Ambiguous", "InvalidResult"} :
             AttemptLogEntryCount(r, attempt, kind)
                 <= HistoryAttemptCount(r, attempt, kind)

AttemptAuthorizationSound ==
    \A i \in 1..Len(attemptLog) :
        attemptLog[i][3] = "Started" =>
            LET r == attemptLog[i][1] IN
                /\ authWitness[r] # NoCap
                /\ Matching(r, authWitness[r])

ExternalEventValueShape ==
    \A i \in 1..Len(externalHistory) :
        IF externalHistory[i][3] = "Success"
        THEN externalHistory[i][4] \in AllowedResults
        ELSE IF externalHistory[i][3] = "InvalidResult"
        THEN externalHistory[i][4] \in Results \ AllowedResults
        ELSE externalHistory[i][4] = NoResult

DeduplicatedOutcomeConsistent ==
    \A r \in DeduplicatedRequests :
        /\ ~(HasHistoryEvent(r, "Success") /\
             HasHistoryEvent(r, "Failure"))
        /\ ~(HasHistoryEvent(r, "Success") /\
             HasHistoryEvent(r, "InvalidResult"))
        /\ ~(HasHistoryEvent(r, "Failure") /\
             HasHistoryEvent(r, "InvalidResult"))

DeduplicatedValueConsistent ==
    \A r \in DeduplicatedRequests :
        /\ Cardinality(SuccessfulValues(r)) <= 1
        /\ Cardinality(InvalidResultValues(r)) <= 1

TerminalEffectClassification ==
    /\ \A r \in Requests :
           phase[r] = "Failed" => PossibleEffectCounts(r) = {0}
    /\ \A r \in Requests \ ReadOnlyRequests :
           phase[r] = "Committed" => PossibleEffectCounts(r) = {1}

FailureKnowledgeSound ==
    /\ \A r \in Requests :
           phase[r] = "Failed" =>
               /\ FailureIsConclusive(r)
               /\ failureAttempt[r] = DurableAttemptCount(r)
               /\ failureAttempt[r] \in 1..MaxAttempts
               /\ AttemptLogEntryCount(
                      r, failureAttempt[r], "Failure") = 1
               /\ HistoryAttemptCount(
                      r, failureAttempt[r], "Failure") = 1
    /\ \A r \in Requests :
           phase[r] # "Failed" => failureAttempt[r] = 0

ValueRefinementSound ==
    /\ \A r \in Requests :
           phase[r] = "Committed" =>
               /\ committedValue[r] \in AllowedResults
               /\ committedValue[r] \in SuccessfulValues(r)
               /\ commitSource[r] \in 1..Len(externalHistory)
               /\ commitAttempt[r] \in 1..MaxAttempts
               /\ externalHistory[commitSource[r]] =
                      ExternalEvent(
                          r, commitAttempt[r], "Success", committedValue[r])
               /\ AttemptLogEntryCount(
                      r, commitAttempt[r], "Success") = 1
    /\ \A r \in Requests :
           phase[r] # "Committed" =>
               /\ committedValue[r] = NoResult
               /\ commitSource[r] = 0
               /\ commitAttempt[r] = 0

ScopeConfinement ==
    \A r \in Requests :
        ~Matching(r, RequestCap(r)) =>
            /\ phase[r] = "New"
            /\ authWitness[r] = NoCap
            /\ DurableAttemptCount(r) = 0
            /\ commitCount[r] = 0

UniqueLogicalCompletion ==
    \A r \in Requests : commitCount[r] <= 1

UncontrolledAtMostOnce ==
    \A r \in Requests :
        RetryClass(r) = "Uncontrolled" => DurableAttemptCount(r) <= 1

CommitLogSound ==
    /\ NoDuplicates(CommitRequests(commitLog))
    /\ \A r \in Requests :
           (r \in SeqRange(CommitRequests(commitLog)))
               <=> (commitCount[r] = 1)
    /\ \A r \in Requests :
           (commitCount[r] = 1) <=> (phase[r] = "Committed")
    /\ \A r \in Requests :
           phase[r] = "Committed" =>
               \E i \in 1..Len(commitLog) :
                   commitLog[i] = CommitEntry(r, committedValue[r])

PhaseHasAuthority ==
    \A r \in Requests :
        (phase[r] = "New") <=> (authWitness[r] = NoCap)

PhaseAttemptConsistency ==
    \A r \in Requests :
        DurableAttemptCount(r) > 0 =>
            phase[r] \in {"Armed", "Committed", "Failed", "Unknown"}

VolatileDisjoint ==
    /\ (crashed \/ recovering) =>
           /\ ready = {}
           /\ inflight = {}
           /\ received = {}
           /\ observedOK = {}
           /\ observedErr = {}
           /\ observedUnknown = {}
    /\ ready \cap inflight = {}
    /\ ready \cap received = {}
    /\ ready \cap observedOK = {}
    /\ ready \cap observedErr = {}
    /\ ready \cap observedUnknown = {}
    /\ inflight \cap received = {}
    /\ inflight \cap observedOK = {}
    /\ inflight \cap observedErr = {}
    /\ inflight \cap observedUnknown = {}
    /\ received \cap observedOK = {}
    /\ received \cap observedErr = {}
    /\ received \cap observedUnknown = {}
    /\ observedOK \cap observedErr = {}
    /\ observedOK \cap observedUnknown = {}
    /\ observedErr \cap observedUnknown = {}
    /\ \A r \in ready \union inflight \union received
                  \union observedOK \union observedErr
                  \union observedUnknown :
           phase[r] = "Armed"
    /\ \A r \in Requests :
           (r \in ready) <=> (readyAttempt[r] > 0)
    /\ \A r \in ready :
           /\ readyAttempt[r] = DurableAttemptCount(r)
           /\ readyAttempt[r] \in 1..MaxAttempts
           /\ AttemptLogEntryCount(
                  r, readyAttempt[r], "Started") = 1
           /\ HistoryAttemptCount(r, readyAttempt[r], "Invoke") = 0
           /\ AttemptLogEntryCount(r, readyAttempt[r], "Success")
              + AttemptLogEntryCount(r, readyAttempt[r], "Failure")
              + AttemptLogEntryCount(r, readyAttempt[r], "Ambiguous")
              + AttemptLogEntryCount(r, readyAttempt[r], "InvalidResult")
                  = 0
    /\ \A r \in Requests :
           (r \in inflight) <=> (inflightAttempt[r] > 0)
    /\ \A r \in inflight :
           /\ inflightAttempt[r] = DurableAttemptCount(r)
           /\ inflightAttempt[r] \in 1..MaxAttempts
           /\ AttemptLogEntryCount(
                  r, inflightAttempt[r], "Started") = 1
           /\ AttemptLogEntryCount(r, inflightAttempt[r], "Success")
              + AttemptLogEntryCount(r, inflightAttempt[r], "Failure")
              + AttemptLogEntryCount(r, inflightAttempt[r], "Ambiguous")
              + AttemptLogEntryCount(r, inflightAttempt[r], "InvalidResult")
                  = 0
           /\ HistoryAttemptCount(r, inflightAttempt[r], "Invoke") = 1
           /\ HistoryAttemptCount(r, inflightAttempt[r], "Success")
              + HistoryAttemptCount(r, inflightAttempt[r], "Failure")
              + HistoryAttemptCount(r, inflightAttempt[r], "Ambiguous")
              + HistoryAttemptCount(r, inflightAttempt[r], "InvalidResult")
                  = 0
    /\ \A r \in Requests :
           (r \in received) <=> (receivedKind[r] \in OutcomeKinds)
    /\ \A r \in Requests :
           (r \in received) <=> (receivedSource[r] > 0)
    /\ \A r \in Requests :
           (r \in received) <=> (receivedAttempt[r] > 0)
    /\ \A r \in Requests \ received : receivedValue[r] = NoResult
    /\ \A r \in received :
           /\ receivedAttempt[r] = DurableAttemptCount(r)
           /\ receivedAttempt[r] \in 1..MaxAttempts
           /\ receivedSource[r] \in 1..Len(externalHistory)
           /\ HistoryAttemptCount(r, receivedAttempt[r], "Invoke") = 1
           /\ externalHistory[receivedSource[r]] =
                  ExternalEvent(
                      r, receivedAttempt[r], receivedKind[r],
                      receivedValue[r])
           /\ AttemptLogEntryCount(r, receivedAttempt[r], "Success")
              + AttemptLogEntryCount(r, receivedAttempt[r], "Failure")
              + AttemptLogEntryCount(r, receivedAttempt[r], "Ambiguous")
              + AttemptLogEntryCount(r, receivedAttempt[r], "InvalidResult")
                  = 0
           /\ IF receivedKind[r] = "Success"
              THEN receivedValue[r] \in AllowedResults
              ELSE IF receivedKind[r] = "InvalidResult"
              THEN receivedValue[r] \in Results \ AllowedResults
              ELSE receivedValue[r] = NoResult
    /\ \A r \in Requests :
           (r \in observedOK) <=> (observedValue[r] # NoResult)
    /\ \A r \in Requests :
           (r \in observedOK) <=> (observedSource[r] > 0)
    /\ \A r \in Requests :
           (r \in observedOK) <=> (observedAttempt[r] > 0)
    /\ \A r \in Requests :
           (r \in observedErr) <=> (observedErrSource[r] > 0)
    /\ \A r \in Requests :
           (r \in observedErr) <=> (observedErrAttempt[r] > 0)
    /\ \A r \in observedOK :
           /\ observedAttempt[r] = DurableAttemptCount(r)
           /\ observedSource[r] \in 1..Len(externalHistory)
           /\ externalHistory[observedSource[r]] =
                  ExternalEvent(
                      r, observedAttempt[r], "Success", observedValue[r])
           /\ AttemptLogEntryCount(
                  r, observedAttempt[r], "Success") = 1
    /\ \A r \in observedErr :
           /\ observedErrAttempt[r] = DurableAttemptCount(r)
           /\ observedErrSource[r] \in 1..Len(externalHistory)
           /\ externalHistory[observedErrSource[r]] =
                  ExternalEvent(
                      r, observedErrAttempt[r], "Failure", NoResult)
           /\ AttemptLogEntryCount(
                  r, observedErrAttempt[r], "Failure") = 1
    /\ \A r \in observedUnknown :
           /\ RetryClass(r) = "Uncontrolled"
           /\ DurableAttemptCount(r) \in 1..MaxAttempts
           /\ AttemptLogEntryCount(
                  r, DurableAttemptCount(r), "Ambiguous")
              + AttemptLogEntryCount(
                  r, DurableAttemptCount(r), "InvalidResult") = 1

BrokerSafety ==
    /\ TypeOK
    /\ CapabilityBudget
    /\ WitnessSound
    /\ AuthLogSound
    /\ InvocationsAuthorized
    /\ AttemptLogWellFormed
    /\ AttemptLogBackedByHistory
    /\ AttemptAuthorizationSound
    /\ ExternalHistoryWellFormed
    /\ ExternalEventValueShape
    /\ DeduplicatedOutcomeConsistent
    /\ DeduplicatedValueConsistent
    /\ TerminalEffectClassification
    /\ FailureKnowledgeSound
    /\ ValueRefinementSound
    /\ ScopeConfinement
    /\ UniqueLogicalCompletion
    /\ UncontrolledAtMostOnce
    /\ CommitLogSound
    /\ PhaseHasAuthority
    /\ PhaseAttemptConsistency
    /\ VolatileDisjoint

====
