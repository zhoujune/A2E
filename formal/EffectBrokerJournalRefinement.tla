---- MODULE EffectBrokerJournalRefinement ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, EffectBrokerParameters

(***************************************************************************
 * Coupled simulation from the typed logical journal to EffectBroker.       *
 *                                                                         *
 * logicalJournal is the implementation-facing durable authority. The       *
 * broker durable variables below are proof-only simulation shadows and are  *
 * constrained to equal EffectBrokerJournal!Replay(logicalJournal). Volatile *
 * execution and ghost interaction state are shared with the abstract       *
 * broker. Each record append is paired with exactly one abstract durable    *
 * transition; physical send/delivery and crash-control actions stutter on   *
 * the journal.                                                              *
 ************************************************************************ ***)

CONSTANTS
    NoRequest,
    NoCap,
    NoResult,
    NoDigest,
    NoKey,
    MaxJournalLength

VARIABLES
    logicalJournal,
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
    logicalJournal, phase, capRemaining, revoked, authWitness, authCount,
    authLog, attemptLog, externalHistory, commitCount, commitLog,
    committedValue, commitSource, commitAttempt, failureAttempt, ready,
    readyAttempt, inflight, inflightAttempt, received, receivedKind,
    receivedValue, receivedSource, receivedAttempt, observedOK,
    observedValue, observedSource, observedAttempt, observedErr,
    observedErrSource, observedErrAttempt, observedUnknown, crashed,
    recovering
>>

Journal == INSTANCE EffectBrokerJournal
    WITH journal <- logicalJournal

Broker == INSTANCE EffectBroker

JournalStutter(action) ==
    /\ action
    /\ UNCHANGED logicalJournal

AppendOne(rec) ==
    /\ Len(logicalJournal) < MaxJournalLength
    /\ rec \in Journal!JournalRecordUniverse
    /\ Journal!RecordEnabled(logicalJournal, rec)
    /\ logicalJournal' = Append(logicalJournal, rec)

AppendAuthorizeRecord(r) ==
    AppendOne(Journal!AuthorizeRecord(r, RequestCap(r)))

AppendRevokeRecord(c) == AppendOne(Journal!RevokeRecord(c))

AppendPrepareRecord(r) ==
    AppendOne(Journal!PrepareRecord(
        r, Journal!AuthorizationIndex(logicalJournal, r)))

AppendArmRecord(r) ==
    AppendOne(Journal!ArmRecord(
        r, Journal!PreparationIndex(logicalJournal, r)))

AppendStartRecord(r) ==
    AppendOne(Journal!StartRecord(
        r, Journal!StartedCount(logicalJournal, r) + 1,
        Journal!ArmIndex(logicalJournal, r)))

AppendOutcomeRecord(r, kind, value) ==
    LET attempt == Journal!LatestAttempt(logicalJournal, r) IN
        AppendOne(Journal!OutcomeRecord(
            r, attempt, Journal!StartIndex(logicalJournal, r, attempt),
            kind, value))

AppendCommitRecord(r, value) ==
    LET attempt == Journal!LatestAttempt(logicalJournal, r) IN
        AppendOne(Journal!CommitRecord(
            r, attempt, Journal!OutcomeIndex(logicalJournal, r, attempt),
            value))

AppendFailRecord(r) ==
    LET attempt == Journal!LatestAttempt(logicalJournal, r) IN
        AppendOne(Journal!FailRecord(
            r, attempt, Journal!OutcomeIndex(logicalJournal, r, attempt)))

AppendUnknownRecord(r, reason) ==
    AppendOne(Journal!UnknownRecord(
        r, Journal!LatestAttempt(logicalJournal, r), reason,
        Journal!LatestEvidenceIndex(logicalJournal, r)))

AppendAuthorize(r) ==
    /\ AppendAuthorizeRecord(r)
    /\ Broker!Authorize(r)

AppendRevoke(c) ==
    /\ AppendRevokeRecord(c)
    /\ Broker!Revoke(c)

AppendPrepare(r) ==
    /\ AppendPrepareRecord(r)
    /\ Broker!Prepare(r)

AppendArm(r) ==
    /\ AppendArmRecord(r)
    /\ Broker!Arm(r)

AppendStart(r) ==
    /\ AppendStartRecord(r)
    /\ Broker!ReserveAttempt(r)

SendAttempt(r, attempt) ==
    JournalStutter(Broker!SendAttempt(r, attempt))

DeliverOK(r, attempt, value) ==
    JournalStutter(Broker!DeliverOK(r, attempt, value))

PersistOK(r) ==
    /\ AppendOutcomeRecord(r, "Success", receivedValue[r])
    /\ Broker!PersistOK(r)

DeliverErr(r, attempt) ==
    JournalStutter(Broker!DeliverErr(r, attempt))

PersistErr(r) ==
    /\ AppendOutcomeRecord(r, "Failure", NoResult)
    /\ Broker!PersistErr(r)

DeliverAmbiguous(r, attempt) ==
    JournalStutter(Broker!DeliverAmbiguous(r, attempt))

PersistAmbiguous(r) ==
    /\ AppendOutcomeRecord(r, "Ambiguous", NoResult)
    /\ Broker!PersistAmbiguous(r)

DeliverInvalidResult(r, attempt, value) ==
    JournalStutter(Broker!DeliverInvalidResult(r, attempt, value))

PersistInvalidResult(r) ==
    /\ AppendOutcomeRecord(r, "InvalidResult", receivedValue[r])
    /\ Broker!PersistInvalidResult(r)

ObservedUnknownReason(r) ==
    LET attempt == Journal!LatestAttempt(logicalJournal, r) IN
        IF Journal!OutcomeKindAt(logicalJournal, r, attempt) = "Ambiguous"
        THEN "AmbiguousOutcome"
        ELSE "InvalidResult"

AppendObservedUnknown(r) ==
    /\ AppendUnknownRecord(r, ObservedUnknownReason(r))
    /\ Broker!RecordObservedUnknown(r)

AppendCommit(r) ==
    /\ AppendCommitRecord(r, observedValue[r])
    /\ Broker!Commit(r)

AppendFailure(r) ==
    /\ AppendFailRecord(r)
    /\ Broker!RecordFailure(r)

AppendNonConclusiveUnknown(r) ==
    /\ AppendUnknownRecord(r, "NonConclusiveFailure")
    /\ Broker!RecordUnknown(r)

RetryAfterUncertainFailure(r) ==
    JournalStutter(Broker!RetryAfterUncertainFailure(r))

AppendRecoveredFailure(r) ==
    /\ AppendFailRecord(r)
    /\ Broker!RecoverRecordedFailure(r)

AppendExhaustedUnknown(r) ==
    /\ AppendUnknownRecord(r, "Exhausted")
    /\ Broker!ExhaustedUnknown(r)

Crash == JournalStutter(Broker!Crash)

BeginRecover == JournalStutter(Broker!BeginRecover)

AppendRecoveryUnknown(r) ==
    /\ AppendUnknownRecord(r, "Recovery")
    /\ Broker!QuarantineUncontrolled(r)

FinishRecover == JournalStutter(Broker!FinishRecover)

Init ==
    /\ logicalJournal = <<>>
    /\ Broker!Init

Next ==
    \/ \E r \in Requests : AppendAuthorize(r)
    \/ \E c \in Caps : AppendRevoke(c)
    \/ \E r \in Requests : AppendPrepare(r)
    \/ \E r \in Requests : AppendArm(r)
    \/ \E r \in Requests : AppendStart(r)
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
    \/ \E r \in Requests : AppendObservedUnknown(r)
    \/ \E r \in Requests : AppendCommit(r)
    \/ \E r \in Requests : AppendFailure(r)
    \/ \E r \in Requests : AppendNonConclusiveUnknown(r)
    \/ \E r \in Requests : RetryAfterUncertainFailure(r)
    \/ \E r \in Requests : AppendRecoveredFailure(r)
    \/ \E r \in Requests : AppendExhaustedUnknown(r)
    \/ Crash
    \/ BeginRecover
    \/ \E r \in Requests : AppendRecoveryUnknown(r)
    \/ FinishRecover

Spec == Init /\ [][Next]_vars

JournalSafety == Journal!JournalSafety
BrokerSafety == Broker!BrokerSafety

ReplayCoupling ==
    LET durable == Journal!Replay(logicalJournal) IN
        /\ phase = durable.phase
        /\ capRemaining = durable.capRemaining
        /\ revoked = durable.revoked
        /\ authWitness = durable.authWitness
        /\ authCount = durable.authCount
        /\ authLog = durable.authLog
        /\ attemptLog = durable.attemptLog
        /\ commitCount = durable.commitCount
        /\ commitLog = durable.commitLog
        /\ committedValue = durable.committedValue
        /\ commitAttempt = durable.commitAttempt
        /\ failureAttempt = durable.failureAttempt

(***************************************************************************
 * TLC checks this temporal property under Spec. ReplayCoupling is the data  *
 * refinement relation; the shared broker shadow and volatile variables give *
 * the explicit action simulation to EffectBroker.                           *
 ************************************************************************ ***)

BrokerRefinement == Broker!Spec
JournalRefinement == Journal!Spec

====
