---- MODULE EffectBrokerJournal ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, EffectBrokerParameters

(***************************************************************************
 * Atomic logical-journal model for the Verified Agent Effect Broker.       *
 *                                                                         *
 * This layer intentionally does not model filesystem frames, flushes,      *
 * crashes, or network delivery. Its only state is a typed append-only      *
 * journal. All durable broker state is reconstructed from that journal.    *
 ************************************************************************ ***)

CONSTANTS
    NoRequest,
    NoCap,
    NoResult,
    NoDigest,
    NoKey,
    MaxJournalLength

Phases == {
    "New", "Authorized", "Prepared", "Armed",
    "Committed", "Failed", "Unknown"
}

RetryClasses == {"ReadOnly", "Idempotent", "Deduplicated", "Uncontrolled"}
OutcomeKinds == {"Success", "Failure", "Ambiguous", "InvalidResult"}
UnknownReasons == {
    "Exhausted", "Recovery", "NonConclusiveFailure",
    "AmbiguousOutcome", "InvalidResult"
}
AttemptKinds == {"Started"} \union OutcomeKinds

ASSUME
    /\ CommonParametersOK
    /\ NoRequest \notin Requests
    /\ NoCap \notin Caps
    /\ NoResult \notin Results
    /\ NoDigest \notin Requests
    /\ NoKey \notin Requests
    /\ MaxJournalLength \in Nat \ {0}

VARIABLE journal

vars == <<journal>>

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

(***************************************************************************
 * The finite model uses the request identifier itself as a symbolic         *
 * immutable request digest and, for deduplicated adapters, stable key.       *
 * A later byte-level refinement replaces these symbols with encodings.       *
 ************************************************************************ ***)

RequestDigest(r) == r

StableKey(r) ==
    IF RetryClass(r) = "Deduplicated" THEN r ELSE NoKey

(***************************************************************************
 * Every record is a uniform ten-field tuple:                                *
 *                                                                           *
 * <<tag, request, capability, attempt, detail, value, ref, auxRef,          *
 *   requestDigest, stableKey>>                                               *
 ************************************************************************ ***)

Tag(rec) == rec[1]
RecRequest(rec) == rec[2]
RecCap(rec) == rec[3]
RecAttempt(rec) == rec[4]
RecDetail(rec) == rec[5]
RecValue(rec) == rec[6]
RecRef(rec) == rec[7]
RecAuxRef(rec) == rec[8]
RecDigest(rec) == rec[9]
RecKey(rec) == rec[10]

AuthorizeRecord(r, c) ==
    <<"Authorize", r, c, 0, "None", NoResult, 0, 0,
      RequestDigest(r), NoKey>>

RevokeRecord(c) ==
    <<"Revoke", NoRequest, c, 0, "None", NoResult, 0, 0,
      NoDigest, NoKey>>

PrepareRecord(r, authRef) ==
    <<"Prepare", r, NoCap, 0, RetryClass(r), NoResult, authRef, 0,
      RequestDigest(r), StableKey(r)>>

ArmRecord(r, prepareRef) ==
    <<"Arm", r, NoCap, 0, "None", NoResult, prepareRef, 0,
      RequestDigest(r), StableKey(r)>>

StartRecord(r, attempt, armRef) ==
    <<"Start", r, NoCap, attempt, "Started", NoResult, armRef, 0,
      RequestDigest(r), StableKey(r)>>

OutcomeRecord(r, attempt, startRef, kind, value) ==
    <<"Outcome", r, NoCap, attempt, kind, value, startRef, 0,
      RequestDigest(r), StableKey(r)>>

CommitRecord(r, attempt, outcomeRef, value) ==
    <<"Commit", r, NoCap, attempt, "Success", value, outcomeRef, 0,
      RequestDigest(r), StableKey(r)>>

FailRecord(r, attempt, outcomeRef) ==
    <<"Fail", r, NoCap, attempt, "Failure", NoResult, outcomeRef, 0,
      RequestDigest(r), StableKey(r)>>

UnknownRecord(r, attempt, reason, evidenceRef) ==
    <<"Unknown", r, NoCap, attempt, reason, NoResult, evidenceRef, 0,
      RequestDigest(r), StableKey(r)>>

Refs == 0..MaxJournalLength

AuthorizeRecordUniverse ==
    {AuthorizeRecord(r, c) : r \in Requests, c \in Caps}

RevokeRecordUniverse ==
    {RevokeRecord(c) : c \in Caps}

PrepareRecordUniverse ==
    {PrepareRecord(r, ref) : r \in Requests, ref \in Refs}

ArmRecordUniverse ==
    {ArmRecord(r, ref) : r \in Requests, ref \in Refs}

StartRecordUniverse ==
    {StartRecord(r, attempt, ref) :
        r \in Requests, attempt \in 1..MaxAttempts, ref \in Refs}

SuccessRecordUniverse ==
    {OutcomeRecord(r, attempt, ref, "Success", value) :
        r \in Requests, attempt \in 1..MaxAttempts,
        ref \in Refs, value \in AllowedResults}

FailureRecordUniverse ==
    {OutcomeRecord(r, attempt, ref, "Failure", NoResult) :
        r \in Requests, attempt \in 1..MaxAttempts, ref \in Refs}

AmbiguousRecordUniverse ==
    {OutcomeRecord(r, attempt, ref, "Ambiguous", NoResult) :
        r \in Requests, attempt \in 1..MaxAttempts, ref \in Refs}

InvalidResultRecordUniverse ==
    {OutcomeRecord(r, attempt, ref, "InvalidResult", value) :
        r \in Requests, attempt \in 1..MaxAttempts,
        ref \in Refs, value \in Results \ AllowedResults}

CommitRecordUniverse ==
    {CommitRecord(r, attempt, ref, value) :
        r \in Requests, attempt \in 1..MaxAttempts,
        ref \in Refs, value \in AllowedResults}

FailRecordUniverse ==
    {FailRecord(r, attempt, ref) :
        r \in Requests, attempt \in 1..MaxAttempts, ref \in Refs}

UnknownRecordUniverse ==
    {UnknownRecord(r, attempt, reason, ref) :
        r \in Requests, attempt \in 0..MaxAttempts,
        reason \in UnknownReasons, ref \in Refs}

JournalRecordUniverse ==
    AuthorizeRecordUniverse
    \union RevokeRecordUniverse
    \union PrepareRecordUniverse
    \union ArmRecordUniverse
    \union StartRecordUniverse
    \union SuccessRecordUniverse
    \union FailureRecordUniverse
    \union AmbiguousRecordUniverse
    \union InvalidResultRecordUniverse
    \union CommitRecordUniverse
    \union FailRecordUniverse
    \union UnknownRecordUniverse

AttemptProjectionUniverse ==
    {<<r, attempt, kind>> :
        r \in Requests, attempt \in 1..MaxAttempts, kind \in AttemptKinds}

Prefix(log, n) ==
    IF n = 0 THEN <<>> ELSE SubSeq(log, 1, n)

RecordIndices(log, tag, r) ==
    {i \in 1..Len(log) :
        /\ Tag(log[i]) = tag
        /\ RecRequest(log[i]) = r}

CapRecordIndices(log, tag, c) ==
    {i \in 1..Len(log) :
        /\ Tag(log[i]) = tag
        /\ RecCap(log[i]) = c}

AttemptRecordIndices(log, tag, r, attempt) ==
    {i \in 1..Len(log) :
        /\ Tag(log[i]) = tag
        /\ RecRequest(log[i]) = r
        /\ RecAttempt(log[i]) = attempt}

UniqueRecordIndex(log, tag, r) ==
    LET indices == RecordIndices(log, tag, r) IN
        IF indices = {} THEN 0 ELSE CHOOSE i \in indices : TRUE

AttemptRecordIndex(log, tag, r, attempt) ==
    LET indices == AttemptRecordIndices(log, tag, r, attempt) IN
        IF indices = {} THEN 0 ELSE CHOOSE i \in indices : TRUE

AuthorizationIndex(log, r) == UniqueRecordIndex(log, "Authorize", r)
PreparationIndex(log, r) == UniqueRecordIndex(log, "Prepare", r)
ArmIndex(log, r) == UniqueRecordIndex(log, "Arm", r)
CommitIndex(log, r) == UniqueRecordIndex(log, "Commit", r)
FailIndex(log, r) == UniqueRecordIndex(log, "Fail", r)
UnknownIndex(log, r) == UniqueRecordIndex(log, "Unknown", r)

StartIndex(log, r, attempt) ==
    AttemptRecordIndex(log, "Start", r, attempt)

OutcomeIndex(log, r, attempt) ==
    AttemptRecordIndex(log, "Outcome", r, attempt)

AuthorizationCount(log, c) ==
    Cardinality(CapRecordIndices(log, "Authorize", c))

StartedCount(log, r) ==
    Cardinality(RecordIndices(log, "Start", r))

OutcomeCount(log, r) ==
    Cardinality(RecordIndices(log, "Outcome", r))

RevokedAt(log) ==
    {c \in Caps : CapRecordIndices(log, "Revoke", c) # {}}

PhaseAt(log, r) ==
    IF CommitIndex(log, r) > 0 THEN "Committed"
    ELSE IF FailIndex(log, r) > 0 THEN "Failed"
    ELSE IF UnknownIndex(log, r) > 0 THEN "Unknown"
    ELSE IF ArmIndex(log, r) > 0 THEN "Armed"
    ELSE IF PreparationIndex(log, r) > 0 THEN "Prepared"
    ELSE IF AuthorizationIndex(log, r) > 0 THEN "Authorized"
    ELSE "New"

AuthWitnessAt(log, r) ==
    LET ref == AuthorizationIndex(log, r) IN
        IF ref = 0 THEN NoCap ELSE RecCap(log[ref])

OutcomeKindAt(log, r, attempt) ==
    LET ref == OutcomeIndex(log, r, attempt) IN
        IF ref = 0 THEN "None" ELSE RecDetail(log[ref])

OutcomeValueAt(log, r, attempt) ==
    LET ref == OutcomeIndex(log, r, attempt) IN
        IF ref = 0 THEN NoResult ELSE RecValue(log[ref])

LatestAttempt(log, r) == StartedCount(log, r)

LatestEvidenceIndex(log, r) ==
    LET attempt == LatestAttempt(log, r) IN
        IF attempt = 0
        THEN ArmIndex(log, r)
        ELSE LET outcomeRef == OutcomeIndex(log, r, attempt) IN
             IF outcomeRef > 0
             THEN outcomeRef
             ELSE StartIndex(log, r, attempt)

AllAttemptsFailed(log, r) ==
    /\ StartedCount(log, r) > 0
    /\ \A attempt \in 1..StartedCount(log, r) :
           OutcomeKindAt(log, r, attempt) = "Failure"

FailureIsConclusive(log, r) ==
    LET attempt == LatestAttempt(log, r) IN
        /\ attempt > 0
        /\ OutcomeKindAt(log, r, attempt) = "Failure"
        /\ (RetryClass(r) = "Idempotent" => AllAttemptsFailed(log, r))

HasDurableSuccess(log, r) ==
    \E attempt \in 1..StartedCount(log, r) :
        OutcomeKindAt(log, r, attempt) = "Success"

EvidenceDecision(log, r) ==
    IF PhaseAt(log, r) # "Armed" THEN "Stable"
    ELSE IF HasDurableSuccess(log, r) THEN "Commit"
    ELSE IF FailureIsConclusive(log, r) THEN "Fail"
    ELSE IF LatestAttempt(log, r) > 0
            /\ OutcomeKindAt(log, r, LatestAttempt(log, r)) = "Failure"
         THEN "Unknown"
    ELSE IF StartedCount(log, r) < MaxAttempts
            /\ (StartedCount(log, r) = 0
                \/ RetryClass(r) # "Uncontrolled")
         THEN "Retry"
    ELSE "Unknown"

HasDurableUncertainty(log, r) ==
    \E attempt \in 1..StartedCount(log, r) :
        OutcomeKindAt(log, r, attempt)
            \in {"None", "Success", "Ambiguous", "InvalidResult"}

CommitValueAt(log, r) ==
    LET ref == CommitIndex(log, r) IN
        IF ref = 0 THEN NoResult ELSE RecValue(log[ref])

CommitAttemptAt(log, r) ==
    LET ref == CommitIndex(log, r) IN
        IF ref = 0 THEN 0 ELSE RecAttempt(log[ref])

FailureAttemptAt(log, r) ==
    LET ref == FailIndex(log, r) IN
        IF ref = 0 THEN 0 ELSE RecAttempt(log[ref])

RECURSIVE AuthProjection(_)
AuthProjection(log) ==
    IF Len(log) = 0
    THEN <<>>
    ELSE LET prior == AuthProjection(Prefix(log, Len(log) - 1))
             rec == log[Len(log)]
         IN IF Tag(rec) = "Authorize"
            THEN Append(prior, <<RecRequest(rec), RecCap(rec)>>)
            ELSE prior

RECURSIVE AttemptProjection(_)
AttemptProjection(log) ==
    IF Len(log) = 0
    THEN <<>>
    ELSE LET prior == AttemptProjection(Prefix(log, Len(log) - 1))
             rec == log[Len(log)]
         IN CASE Tag(rec) = "Start" ->
                    Append(prior,
                        <<RecRequest(rec), RecAttempt(rec), "Started">>)
            [] Tag(rec) = "Outcome" ->
                    Append(prior,
                        <<RecRequest(rec), RecAttempt(rec), RecDetail(rec)>>)
            [] OTHER -> prior

RECURSIVE CommitProjection(_)
CommitProjection(log) ==
    IF Len(log) = 0
    THEN <<>>
    ELSE LET prior == CommitProjection(Prefix(log, Len(log) - 1))
             rec == log[Len(log)]
         IN IF Tag(rec) = "Commit"
            THEN Append(prior, <<RecRequest(rec), RecValue(rec)>>)
            ELSE prior

Replay(log) ==
    [ phase |-> [r \in Requests |-> PhaseAt(log, r)],
      capRemaining |->
          [c \in Caps |->
              InitialBudget(c) - AuthorizationCount(log, c)],
      revoked |-> RevokedAt(log),
      authWitness |-> [r \in Requests |-> AuthWitnessAt(log, r)],
      authCount |-> [c \in Caps |-> AuthorizationCount(log, c)],
      authLog |-> AuthProjection(log),
      attemptLog |-> AttemptProjection(log),
      commitCount |->
          [r \in Requests |-> IF CommitIndex(log, r) = 0 THEN 0 ELSE 1],
      commitLog |-> CommitProjection(log),
      committedValue |-> [r \in Requests |-> CommitValueAt(log, r)],
      commitAttempt |-> [r \in Requests |-> CommitAttemptAt(log, r)],
      failureAttempt |-> [r \in Requests |-> FailureAttemptAt(log, r)],
      prepareRef |-> [r \in Requests |-> PreparationIndex(log, r)],
      armRef |-> [r \in Requests |-> ArmIndex(log, r)] ]

OutcomeValueShape(kind, value) ==
    CASE kind = "Success" -> value \in AllowedResults
    [] kind = "InvalidResult" -> value \in Results \ AllowedResults
    [] OTHER -> value = NoResult

RecordEnabled(log, rec) ==
    LET tag == Tag(rec)
        r == RecRequest(rec)
        c == RecCap(rec)
        attempt == RecAttempt(rec)
        detail == RecDetail(rec)
        value == RecValue(rec)
        ref == RecRef(rec)
    IN CASE tag = "Authorize" ->
                /\ PhaseAt(log, r) = "New"
                /\ c = RequestCap(r)
                /\ Matching(r, c)
                /\ c \notin RevokedAt(log)
                /\ AuthorizationCount(log, c) < InitialBudget(c)
                /\ rec = AuthorizeRecord(r, c)
       [] tag = "Revoke" ->
                /\ c \notin RevokedAt(log)
                /\ rec = RevokeRecord(c)
       [] tag = "Prepare" ->
                /\ PhaseAt(log, r) = "Authorized"
                /\ ref = AuthorizationIndex(log, r)
                /\ ref > 0
                /\ rec = PrepareRecord(r, ref)
       [] tag = "Arm" ->
                /\ PhaseAt(log, r) = "Prepared"
                /\ ref = PreparationIndex(log, r)
                /\ ref > 0
                /\ rec = ArmRecord(r, ref)
       [] tag = "Start" ->
                /\ PhaseAt(log, r) = "Armed"
                /\ StartedCount(log, r) < MaxAttempts
                /\ attempt = StartedCount(log, r) + 1
                /\ ref = ArmIndex(log, r)
                /\ ref > 0
                /\ EvidenceDecision(log, r) = "Retry"
                /\ (RetryClass(r) = "Uncontrolled" =>
                        StartedCount(log, r) = 0)
                /\ rec = StartRecord(r, attempt, ref)
       [] tag = "Outcome" ->
                /\ PhaseAt(log, r) = "Armed"
                /\ attempt = LatestAttempt(log, r)
                /\ attempt > 0
                /\ OutcomeIndex(log, r, attempt) = 0
                /\ ref = StartIndex(log, r, attempt)
                /\ ref > 0
                /\ detail \in OutcomeKinds
                /\ OutcomeValueShape(detail, value)
                /\ rec = OutcomeRecord(r, attempt, ref, detail, value)
       [] tag = "Commit" ->
                /\ PhaseAt(log, r) = "Armed"
                /\ EvidenceDecision(log, r) = "Commit"
                /\ attempt = LatestAttempt(log, r)
                /\ attempt > 0
                /\ ref = OutcomeIndex(log, r, attempt)
                /\ ref > 0
                /\ OutcomeKindAt(log, r, attempt) = "Success"
                /\ value = OutcomeValueAt(log, r, attempt)
                /\ rec = CommitRecord(r, attempt, ref, value)
       [] tag = "Fail" ->
                /\ PhaseAt(log, r) = "Armed"
                /\ EvidenceDecision(log, r) = "Fail"
                /\ attempt = LatestAttempt(log, r)
                /\ attempt > 0
                /\ ref = OutcomeIndex(log, r, attempt)
                /\ ref > 0
                /\ FailureIsConclusive(log, r)
                /\ rec = FailRecord(r, attempt, ref)
       [] tag = "Unknown" ->
                /\ PhaseAt(log, r) = "Armed"
                /\ EvidenceDecision(log, r) = "Unknown"
                /\ attempt = LatestAttempt(log, r)
                /\ ref = LatestEvidenceIndex(log, r)
                /\ ref > 0
                /\ CASE detail = "Exhausted" ->
                            /\ attempt = MaxAttempts
                            /\ HasDurableUncertainty(log, r)
                   [] detail = "Recovery" ->
                            /\ RetryClass(r) = "Uncontrolled"
                            /\ ~FailureIsConclusive(log, r)
                            /\ ~HasDurableSuccess(log, r)
                   [] detail = "NonConclusiveFailure" ->
                            /\ attempt > 0
                            /\ OutcomeKindAt(log, r, attempt) = "Failure"
                            /\ ~FailureIsConclusive(log, r)
                   [] detail = "AmbiguousOutcome" ->
                            /\ RetryClass(r) = "Uncontrolled"
                            /\ attempt > 0
                            /\ OutcomeKindAt(log, r, attempt) = "Ambiguous"
                   [] detail = "InvalidResult" ->
                            /\ RetryClass(r) = "Uncontrolled"
                            /\ attempt > 0
                            /\ OutcomeKindAt(log, r, attempt) = "InvalidResult"
                   [] OTHER -> FALSE
                /\ rec = UnknownRecord(r, attempt, detail, ref)
       [] OTHER -> FALSE

AppendOne(rec) ==
    /\ Len(journal) < MaxJournalLength
    /\ rec \in JournalRecordUniverse
    /\ RecordEnabled(journal, rec)
    /\ journal' = Append(journal, rec)

AppendAuthorize(r) == AppendOne(AuthorizeRecord(r, RequestCap(r)))

AppendRevoke(c) == AppendOne(RevokeRecord(c))

AppendPrepare(r) ==
    AppendOne(PrepareRecord(r, AuthorizationIndex(journal, r)))

AppendArm(r) ==
    AppendOne(ArmRecord(r, PreparationIndex(journal, r)))

AppendStart(r) ==
    AppendOne(StartRecord(
        r, StartedCount(journal, r) + 1, ArmIndex(journal, r)))

AppendOutcome(r, kind, value) ==
    LET attempt == LatestAttempt(journal, r) IN
        AppendOne(OutcomeRecord(
            r, attempt, StartIndex(journal, r, attempt), kind, value))

AppendCommit(r, value) ==
    LET attempt == LatestAttempt(journal, r) IN
        AppendOne(CommitRecord(
            r, attempt, OutcomeIndex(journal, r, attempt), value))

AppendFail(r) ==
    LET attempt == LatestAttempt(journal, r) IN
        AppendOne(FailRecord(
            r, attempt, OutcomeIndex(journal, r, attempt)))

AppendUnknown(r, reason) ==
    AppendOne(UnknownRecord(
        r, LatestAttempt(journal, r), reason,
        LatestEvidenceIndex(journal, r)))

Init == journal = <<>>

Next ==
    \/ \E r \in Requests : AppendAuthorize(r)
    \/ \E c \in Caps : AppendRevoke(c)
    \/ \E r \in Requests : AppendPrepare(r)
    \/ \E r \in Requests : AppendArm(r)
    \/ \E r \in Requests : AppendStart(r)
    \/ \E r \in Requests, value \in AllowedResults :
           AppendOutcome(r, "Success", value)
    \/ \E r \in Requests : AppendOutcome(r, "Failure", NoResult)
    \/ \E r \in Requests : AppendOutcome(r, "Ambiguous", NoResult)
    \/ \E r \in Requests, value \in Results \ AllowedResults :
           AppendOutcome(r, "InvalidResult", value)
    \/ \E r \in Requests, value \in AllowedResults :
           AppendCommit(r, value)
    \/ \E r \in Requests : AppendFail(r)
    \/ \E r \in Requests, reason \in UnknownReasons :
           AppendUnknown(r, reason)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Journal and replay invariants.                                           *
 ************************************************************************ ***)

TypeOK ==
    /\ journal \in Seq(JournalRecordUniverse)
    /\ Len(journal) <= MaxJournalLength

ReplayTypeOK ==
    LET durable == Replay(journal) IN
        /\ durable.phase \in [Requests -> Phases]
        /\ durable.capRemaining \in [Caps -> Nat]
        /\ durable.revoked \subseteq Caps
        /\ durable.authWitness \in [Requests -> Caps \union {NoCap}]
        /\ durable.authCount \in [Caps -> Nat]
        /\ durable.authLog \in Seq(Requests \X Caps)
        /\ durable.attemptLog \in Seq(AttemptProjectionUniverse)
        /\ durable.commitCount \in [Requests -> 0..1]
        /\ durable.commitLog \in Seq(Requests \X Results)
        /\ durable.committedValue
               \in [Requests -> Results \union {NoResult}]
        /\ durable.commitAttempt \in [Requests -> 0..MaxAttempts]
        /\ durable.failureAttempt \in [Requests -> 0..MaxAttempts]
        /\ durable.prepareRef \in [Requests -> 0..MaxJournalLength]
        /\ durable.armRef \in [Requests -> 0..MaxJournalLength]

EveryPrefixLegal ==
    \A i \in 1..Len(journal) :
        RecordEnabled(Prefix(journal, i - 1), journal[i])

ReferencesPointBackward ==
    \A i \in 1..Len(journal) :
        Tag(journal[i])
            \in {"Prepare", "Arm", "Start", "Outcome",
                 "Commit", "Fail", "Unknown"} =>
            RecRef(journal[i]) \in 1..(i - 1)

ReferenceTargetsSound ==
    \A i \in 1..Len(journal) :
        LET rec == journal[i]
            r == RecRequest(rec)
            attempt == RecAttempt(rec)
            ref == RecRef(rec)
        IN CASE Tag(rec) = "Prepare" ->
                    /\ journal[ref] =
                           AuthorizeRecord(r, RequestCap(r))
           [] Tag(rec) = "Arm" ->
                    journal[ref] =
                        PrepareRecord(r, AuthorizationIndex(journal, r))
           [] Tag(rec) = "Start" ->
                    journal[ref] =
                        ArmRecord(r, PreparationIndex(journal, r))
           [] Tag(rec) = "Outcome" ->
                    journal[ref] =
                        StartRecord(r, attempt, ArmIndex(journal, r))
           [] Tag(rec) = "Commit" ->
                    journal[ref] =
                        OutcomeRecord(
                            r, attempt, StartIndex(journal, r, attempt),
                            "Success", RecValue(rec))
           [] Tag(rec) = "Fail" ->
                    journal[ref] =
                        OutcomeRecord(
                            r, attempt, StartIndex(journal, r, attempt),
                            "Failure", NoResult)
           [] Tag(rec) = "Unknown" ->
                    /\ RecRequest(journal[ref]) = r
                    /\ Tag(journal[ref]) \in {"Arm", "Start", "Outcome"}
           [] OTHER -> TRUE

RecordBindingsStable ==
    \A i \in 1..Len(journal) :
        LET rec == journal[i] IN
            IF RecRequest(rec) \in Requests
            THEN /\ RecDigest(rec) = RequestDigest(RecRequest(rec))
                 /\ (RecKey(rec) = StableKey(RecRequest(rec))
                       \/ Tag(rec) = "Authorize")
            ELSE /\ Tag(rec) = "Revoke"
                 /\ RecDigest(rec) = NoDigest
                 /\ RecKey(rec) = NoKey

UniqueLifecycleRecords ==
    /\ \A c \in Caps :
           Cardinality(CapRecordIndices(journal, "Revoke", c)) <= 1
    /\ \A r \in Requests :
           /\ Cardinality(RecordIndices(journal, "Authorize", r)) <= 1
           /\ Cardinality(RecordIndices(journal, "Prepare", r)) <= 1
           /\ Cardinality(RecordIndices(journal, "Arm", r)) <= 1
           /\ Cardinality(RecordIndices(journal, "Commit", r)) <= 1
           /\ Cardinality(RecordIndices(journal, "Fail", r)) <= 1
           /\ Cardinality(RecordIndices(journal, "Unknown", r)) <= 1
           /\ Cardinality(
                  RecordIndices(journal, "Commit", r)
                  \union RecordIndices(journal, "Fail", r)
                  \union RecordIndices(journal, "Unknown", r)) <= 1

CapabilityBudget ==
    LET durable == Replay(journal) IN
        \A c \in Caps :
            durable.authCount[c] + durable.capRemaining[c]
                = InitialBudget(c)

AuthorizationReplaySound ==
    LET durable == Replay(journal) IN
        /\ \A r \in Requests :
               (durable.authWitness[r] # NoCap) <=>
                   AuthorizationIndex(journal, r) > 0
        /\ \A r \in Requests :
               durable.authWitness[r] # NoCap =>
                   Matching(r, durable.authWitness[r])

AttemptReplaySound ==
    /\ \A r \in Requests : StartedCount(journal, r) <= MaxAttempts
    /\ \A r \in Requests, attempt \in 1..MaxAttempts :
           /\ Cardinality(
                  AttemptRecordIndices(journal, "Start", r, attempt)) <= 1
           /\ Cardinality(
                  AttemptRecordIndices(journal, "Outcome", r, attempt)) <= 1
           /\ OutcomeIndex(journal, r, attempt) > 0 =>
                  StartIndex(journal, r, attempt) > 0
    /\ \A r \in Requests :
           \A attempt \in 1..StartedCount(journal, r) :
               StartIndex(journal, r, attempt) > 0

TerminalReplaySound ==
    LET durable == Replay(journal) IN
        /\ \A r \in Requests :
               durable.phase[r] = "Committed" =>
                   LET attempt == durable.commitAttempt[r]
                       outcomeRef == OutcomeIndex(journal, r, attempt)
                   IN /\ durable.committedValue[r] \in AllowedResults
                      /\ outcomeRef > 0
                      /\ OutcomeKindAt(journal, r, attempt) = "Success"
                      /\ OutcomeValueAt(journal, r, attempt)
                             = durable.committedValue[r]
        /\ \A r \in Requests :
               durable.phase[r] = "Failed" =>
                   LET attempt == durable.failureAttempt[r] IN
                       /\ attempt \in 1..MaxAttempts
                       /\ OutcomeKindAt(journal, r, attempt) = "Failure"
                       /\ FailureIsConclusive(journal, r)
        /\ \A r \in Requests :
               durable.phase[r] \notin {"Committed", "Failed"} =>
                   /\ durable.committedValue[r] = NoResult
                   /\ durable.commitAttempt[r] = 0
                   /\ durable.failureAttempt[r] = 0

NoRecordsAfterTerminal ==
    \A r \in Requests :
        LET terminalRefs ==
                RecordIndices(journal, "Commit", r)
                \union RecordIndices(journal, "Fail", r)
                \union RecordIndices(journal, "Unknown", r)
        IN terminalRefs # {} =>
            LET terminalRef == CHOOSE i \in terminalRefs : TRUE IN
                \A j \in (terminalRef + 1)..Len(journal) :
                    RecRequest(journal[j]) # r

JournalSafety ==
    /\ TypeOK
    /\ ReplayTypeOK
    /\ EveryPrefixLegal
    /\ ReferencesPointBackward
    /\ ReferenceTargetsSound
    /\ RecordBindingsStable
    /\ UniqueLifecycleRecords
    /\ CapabilityBudget
    /\ AuthorizationReplaySound
    /\ AttemptReplaySound
    /\ TerminalReplaySound
    /\ NoRecordsAfterTerminal

====
