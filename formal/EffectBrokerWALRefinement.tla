---- MODULE EffectBrokerWALRefinement ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, EffectBrokerParameters

(***************************************************************************
 * Composed BrokerContext[WAL] model.                                       *
 *                                                                         *
 * A record is staged while EffectBroker stutters. Completing a Full frame  *
 * is the atomic Journal and abstract Broker linearization point. FlushAck   *
 * releases the operation to subsequent runtime actions. A crash discards   *
 * staged or torn work, preserves complete frames, and clears Broker         *
 * volatile state.                                                          *
 ************************************************************************ ***)

CONSTANTS
    NoRequest,
    NoCap,
    NoResult,
    NoDigest,
    NoKey,
    MaxJournalLength

VARIABLES
    cache,
    media,
    ackedLen,
    ackHistory,
    pending,
    shadowJournal,
    scanPhase,
    scanResult,
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

walStorageVars == <<
    cache, media, ackedLen, ackHistory, pending, shadowJournal, scanPhase,
    scanResult
>>

brokerVars == <<
    phase, capRemaining, revoked, authWitness, authCount, authLog,
    attemptLog, externalHistory, commitCount, commitLog, committedValue,
    commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
    inflight, inflightAttempt, received, receivedKind, receivedValue,
    receivedSource, receivedAttempt, observedOK, observedValue,
    observedSource, observedAttempt, observedErr, observedErrSource,
    observedErrAttempt, observedUnknown, crashed, recovering
>>

vars == <<
    cache, media, ackedLen, ackHistory, pending, shadowJournal, scanPhase,
    scanResult, phase, capRemaining, revoked, authWitness, authCount, authLog,
    attemptLog, externalHistory, commitCount, commitLog, committedValue,
    commitSource, commitAttempt, failureAttempt, ready, readyAttempt,
    inflight, inflightAttempt, received, receivedKind, receivedValue,
    receivedSource, receivedAttempt, observedOK, observedValue,
    observedSource, observedAttempt, observedErr, observedErrSource,
    observedErrAttempt, observedUnknown, crashed, recovering
>>

Journal == INSTANCE EffectBrokerJournal
    WITH journal <- shadowJournal

WAL == INSTANCE EffectBrokerWAL

Broker == INSTANCE EffectBroker

AuthorizeRec(r) ==
    Journal!AuthorizeRecord(r, RequestCap(r))

RevokeRec(c) == Journal!RevokeRecord(c)

PrepareRec(r) ==
    Journal!PrepareRecord(
        r, Journal!AuthorizationIndex(shadowJournal, r))

ArmRec(r) ==
    Journal!ArmRecord(
        r, Journal!PreparationIndex(shadowJournal, r))

StartRec(r) ==
    Journal!StartRecord(
        r, Journal!StartedCount(shadowJournal, r) + 1,
        Journal!ArmIndex(shadowJournal, r))

OutcomeRec(r, kind, value) ==
    LET attempt == Journal!LatestAttempt(shadowJournal, r) IN
        Journal!OutcomeRecord(
            r, attempt, Journal!StartIndex(shadowJournal, r, attempt),
            kind, value)

CommitRec(r) ==
    LET attempt == Journal!LatestAttempt(shadowJournal, r) IN
        Journal!CommitRecord(
            r, attempt, Journal!OutcomeIndex(shadowJournal, r, attempt),
            observedValue[r])

FailRec(r) ==
    LET attempt == Journal!LatestAttempt(shadowJournal, r) IN
        Journal!FailRecord(
            r, attempt, Journal!OutcomeIndex(shadowJournal, r, attempt))

UnknownRec(r, reason) ==
    Journal!UnknownRecord(
        r, Journal!LatestAttempt(shadowJournal, r), reason,
        Journal!LatestEvidenceIndex(shadowJournal, r))

ObservedUnknownReason(r) ==
    LET attempt == Journal!LatestAttempt(shadowJournal, r) IN
        IF Journal!OutcomeKindAt(shadowJournal, r, attempt) = "Ambiguous"
        THEN "AmbiguousOutcome"
        ELSE "InvalidResult"

StageRecord(rec, brokerAction) ==
    /\ ENABLED brokerAction
    /\ WAL!Stage(rec)
    /\ UNCHANGED brokerVars

StageAuthorize(r) ==
    StageRecord(AuthorizeRec(r), Broker!Authorize(r))

StageRevoke(c) ==
    StageRecord(RevokeRec(c), Broker!Revoke(c))

StagePrepare(r) ==
    StageRecord(PrepareRec(r), Broker!Prepare(r))

StageArm(r) ==
    StageRecord(ArmRec(r), Broker!Arm(r))

StageStart(r) ==
    StageRecord(StartRec(r), Broker!ReserveAttempt(r))

StageOK(r) ==
    StageRecord(
        OutcomeRec(r, "Success", receivedValue[r]),
        Broker!PersistOK(r))

StageErr(r) ==
    StageRecord(
        OutcomeRec(r, "Failure", NoResult),
        Broker!PersistErr(r))

StageAmbiguous(r) ==
    StageRecord(
        OutcomeRec(r, "Ambiguous", NoResult),
        Broker!PersistAmbiguous(r))

StageInvalidResult(r) ==
    StageRecord(
        OutcomeRec(r, "InvalidResult", receivedValue[r]),
        Broker!PersistInvalidResult(r))

StageObservedUnknown(r) ==
    StageRecord(
        UnknownRec(r, ObservedUnknownReason(r)),
        Broker!RecordObservedUnknown(r))

StageCommit(r) ==
    StageRecord(CommitRec(r), Broker!Commit(r))

FailureAction(r) ==
    IF recovering
    THEN Broker!RecoverRecordedFailure(r)
    ELSE Broker!RecordFailure(r)

StageFailure(r) ==
    StageRecord(FailRec(r), FailureAction(r))

StageNonConclusiveUnknown(r) ==
    StageRecord(
        UnknownRec(r, "NonConclusiveFailure"),
        Broker!RecordUnknown(r))

StageExhaustedUnknown(r) ==
    StageRecord(
        UnknownRec(r, "Exhausted"),
        Broker!ExhaustedUnknown(r))

StageRecoveryUnknown(r) ==
    StageRecord(
        UnknownRec(r, "Recovery"),
        Broker!QuarantineUncontrolled(r))

ApplyRecord(rec) ==
    LET tag == Journal!Tag(rec)
        r == Journal!RecRequest(rec)
        c == Journal!RecCap(rec)
        detail == Journal!RecDetail(rec)
    IN CASE tag = "Authorize" -> Broker!Authorize(r)
       [] tag = "Revoke" -> Broker!Revoke(c)
       [] tag = "Prepare" -> Broker!Prepare(r)
       [] tag = "Arm" -> Broker!Arm(r)
       [] tag = "Start" -> Broker!ReserveAttempt(r)
       [] tag = "Outcome" ->
              CASE detail = "Success" -> Broker!PersistOK(r)
              [] detail = "Failure" -> Broker!PersistErr(r)
              [] detail = "Ambiguous" -> Broker!PersistAmbiguous(r)
              [] detail = "InvalidResult" ->
                     Broker!PersistInvalidResult(r)
              [] OTHER -> FALSE
       [] tag = "Commit" -> Broker!Commit(r)
       [] tag = "Fail" -> FailureAction(r)
       [] tag = "Unknown" ->
              CASE detail = "NonConclusiveFailure" -> Broker!RecordUnknown(r)
              [] detail = "AmbiguousOutcome" ->
                     Broker!RecordObservedUnknown(r)
              [] detail = "InvalidResult" ->
                     Broker!RecordObservedUnknown(r)
              [] detail = "Exhausted" -> Broker!ExhaustedUnknown(r)
              [] detail = "Recovery" -> Broker!QuarantineUncontrolled(r)
              [] OTHER -> FALSE
       [] OTHER -> FALSE

CompleteFull ==
    /\ WAL!WriteFull
    /\ ApplyRecord(pending[1])

WriteTorn ==
    /\ WAL!WriteTorn
    /\ UNCHANGED brokerVars

CompleteTorn ==
    /\ WAL!FinishTorn
    /\ ApplyRecord(pending[1])

FlushAck ==
    /\ WAL!FlushAck
    /\ UNCHANGED brokerVars

WALQuiescent ==
    /\ pending = <<>>
    /\ cache = shadowJournal
    /\ ackedLen = Len(cache)
    /\ WAL!NoTornFrame
    /\ scanPhase = "Idle"

SendAttempt(r, attempt) ==
    /\ WALQuiescent
    /\ Broker!SendAttempt(r, attempt)
    /\ UNCHANGED walStorageVars

DeliverOK(r, attempt, value) ==
    /\ WALQuiescent
    /\ Broker!DeliverOK(r, attempt, value)
    /\ UNCHANGED walStorageVars

DeliverErr(r, attempt) ==
    /\ WALQuiescent
    /\ Broker!DeliverErr(r, attempt)
    /\ UNCHANGED walStorageVars

DeliverAmbiguous(r, attempt) ==
    /\ WALQuiescent
    /\ Broker!DeliverAmbiguous(r, attempt)
    /\ UNCHANGED walStorageVars

DeliverInvalidResult(r, attempt, value) ==
    /\ WALQuiescent
    /\ Broker!DeliverInvalidResult(r, attempt, value)
    /\ UNCHANGED walStorageVars

RetryAfterUncertainFailure(r) ==
    /\ WALQuiescent
    /\ Broker!RetryAfterUncertainFailure(r)
    /\ UNCHANGED walStorageVars

Crash ==
    /\ WAL!Crash
    /\ Broker!Crash

BeginScan ==
    /\ WAL!BeginScan
    /\ UNCHANGED brokerVars

FinishScan ==
    /\ WAL!FinishScan
    /\ UNCHANGED brokerVars

TruncateTail ==
    /\ WAL!TruncateTail
    /\ UNCHANGED brokerVars

AbortScan ==
    /\ WAL!AbortScan
    /\ UNCHANGED brokerVars

BeginRecover ==
    /\ WAL!BeginRecover
    /\ Broker!BeginRecover

FinishRecover ==
    /\ WAL!FinishRecover
    /\ Broker!FinishRecover

Init ==
    /\ WAL!Init
    /\ Broker!Init

Next ==
    \/ \E r \in Requests : StageAuthorize(r)
    \/ \E c \in Caps : StageRevoke(c)
    \/ \E r \in Requests : StagePrepare(r)
    \/ \E r \in Requests : StageArm(r)
    \/ \E r \in Requests : StageStart(r)
    \/ \E r \in Requests : StageOK(r)
    \/ \E r \in Requests : StageErr(r)
    \/ \E r \in Requests : StageAmbiguous(r)
    \/ \E r \in Requests : StageInvalidResult(r)
    \/ \E r \in Requests : StageObservedUnknown(r)
    \/ \E r \in Requests : StageCommit(r)
    \/ \E r \in Requests : StageFailure(r)
    \/ \E r \in Requests : StageNonConclusiveUnknown(r)
    \/ \E r \in Requests : StageExhaustedUnknown(r)
    \/ \E r \in Requests : StageRecoveryUnknown(r)
    \/ CompleteFull
    \/ WriteTorn
    \/ CompleteTorn
    \/ FlushAck
    \/ \E r \in Requests, attempt \in 1..MaxAttempts :
           SendAttempt(r, attempt)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts,
          value \in AllowedResults : DeliverOK(r, attempt, value)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts :
           DeliverErr(r, attempt)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts :
           DeliverAmbiguous(r, attempt)
    \/ \E r \in Requests, attempt \in 1..MaxAttempts,
          value \in Results \ AllowedResults :
           DeliverInvalidResult(r, attempt, value)
    \/ Crash
    \/ BeginScan
    \/ FinishScan
    \/ TruncateTail
    \/ AbortScan
    \/ BeginRecover
    \/ FinishRecover

Spec == Init /\ [][Next]_vars

ReplayCoupling ==
    LET durable == Journal!Replay(shadowJournal) IN
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

StartAcknowledged(r, attempt) ==
    \E i \in 1..Len(ackHistory) :
        /\ Journal!Tag(ackHistory[i]) = "Start"
        /\ Journal!RecRequest(ackHistory[i]) = r
        /\ Journal!RecAttempt(ackHistory[i]) = attempt

InvocationsAcknowledged ==
    \A i \in 1..Len(externalHistory) :
        externalHistory[i][3] = "Invoke" =>
            StartAcknowledged(
                externalHistory[i][1], externalHistory[i][2])

RecoveryPendingSound ==
    (recovering /\ Len(pending) = 1) =>
        \/ Journal!Tag(pending[1]) = "Fail"
        \/ /\ Journal!Tag(pending[1]) = "Unknown"
           /\ Journal!RecDetail(pending[1]) = "Recovery"

FinishRecoverGuardSound ==
    ENABLED FinishRecover =>
        /\ recovering
        /\ WALQuiescent
        /\ Broker!RecoveryComplete

MediaReplayCoupling ==
    /\ shadowJournal = WAL!Parse(media)
    /\ ReplayCoupling

WALSafety == WAL!WALSafety
JournalSafety == Journal!JournalSafety
BrokerSafety == Broker!BrokerSafety

WALProjection == WAL!Spec
JournalProjection == Journal!Spec
BrokerProjection == Broker!Spec

====
