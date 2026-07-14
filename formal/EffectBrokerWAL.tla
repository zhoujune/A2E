---- MODULE EffectBrokerWAL ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, EffectBrokerParameters

(***************************************************************************
 * Physical write-ahead-log refinement of EffectBrokerJournal.              *
 *                                                                         *
 * cache is the process-visible append buffer. media is crash-stable framed *
 * storage and may end in one torn frame. A complete frame is the logical   *
 * journal linearization point; FlushAck only tells the process that the     *
 * already complete prefix is durable.                                      *
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
    crashed,
    recovering

vars == <<
    cache, media, ackedLen, ackHistory, pending, shadowJournal, crashed,
    recovering, scanPhase, scanResult
>>

Journal == INSTANCE EffectBrokerJournal
    WITH journal <- shadowJournal

Online == ~crashed

ScanPhases == {"Idle", "Scanning", "Scanned", "Truncated"}

FullFrame(lsn, rec) == <<"Full", lsn, rec>>
TornFrame(lsn, rec) == <<"Torn", lsn, rec>>

FrameKind(frame) == frame[1]
FrameLSN(frame) == frame[2]
FrameRecord(frame) == frame[3]

FrameUniverse ==
    {FullFrame(lsn, rec) :
        lsn \in 1..MaxJournalLength,
        rec \in Journal!JournalRecordUniverse}
    \union
    {TornFrame(lsn, rec) :
        lsn \in 1..MaxJournalLength,
        rec \in Journal!JournalRecordUniverse}

Prefix(seq, n) ==
    IF n = 0 THEN <<>> ELSE SubSeq(seq, 1, n)

IsPrefix(prefix, seq) ==
    /\ Len(prefix) <= Len(seq)
    /\ prefix = Prefix(seq, Len(prefix))

RECURSIVE Parse(_)
Parse(frames) ==
    IF Len(frames) = 0
    THEN <<>>
    ELSE LET first == frames[1] IN
         IF FrameKind(first) = "Full"
         THEN <<FrameRecord(first)>> \o Parse(Tail(frames))
         ELSE <<>>

FullFrames(log) ==
    IF Len(log) = 0
    THEN <<>>
    ELSE [i \in 1..Len(log) |-> FullFrame(i, log[i])]

NoTornFrame ==
    \A i \in 1..Len(media) : FrameKind(media[i]) = "Full"

HasTornTail ==
    /\ Len(media) > 0
    /\ FrameKind(media[Len(media)]) = "Torn"

CanWritePending ==
    /\ Online
    /\ Len(pending) = 1
    /\ NoTornFrame
    /\ Len(cache) = ackedLen + 1
    /\ Len(shadowJournal) = ackedLen
    /\ Len(media) = Len(shadowJournal)
    /\ pending[1] = cache[Len(cache)]

Stage(rec) ==
    /\ Online
    /\ pending = <<>>
    /\ Len(cache) < MaxJournalLength
    /\ rec \in Journal!JournalRecordUniverse
    /\ Journal!RecordEnabled(shadowJournal, rec)
    /\ cache' = Append(cache, rec)
    /\ pending' = <<rec>>
    /\ UNCHANGED <<
           media, ackedLen, ackHistory, shadowJournal, scanPhase, scanResult,
           crashed, recovering
       >>

WriteFull ==
    /\ CanWritePending
    /\ media' = Append(
           media, FullFrame(Len(media) + 1, pending[1]))
    /\ shadowJournal' = Append(shadowJournal, pending[1])
    /\ UNCHANGED <<
           cache, ackedLen, ackHistory, pending, scanPhase, scanResult,
           crashed, recovering
       >>

WriteTorn ==
    /\ CanWritePending
    /\ media' = Append(
           media, TornFrame(Len(media) + 1, pending[1]))
    /\ UNCHANGED <<
           cache, ackedLen, ackHistory, pending, shadowJournal, crashed,
           recovering, scanPhase, scanResult
       >>

FinishTorn ==
    /\ Online
    /\ Len(pending) = 1
    /\ HasTornTail
    /\ Len(cache) = ackedLen + 1
    /\ Len(shadowJournal) = ackedLen
    /\ Len(media) = Len(cache)
    /\ FrameLSN(media[Len(media)]) = Len(media)
    /\ FrameRecord(media[Len(media)]) = pending[1]
    /\ pending[1] = cache[Len(cache)]
    /\ media' =
           [media EXCEPT
               ![Len(media)] =
                   FullFrame(Len(media), pending[1])]
    /\ shadowJournal' = Append(shadowJournal, pending[1])
    /\ UNCHANGED <<
           cache, ackedLen, ackHistory, pending, scanPhase, scanResult,
           crashed, recovering
       >>

FlushAck ==
    /\ Online
    /\ Len(pending) = 1
    /\ NoTornFrame
    /\ cache = shadowJournal
    /\ Len(media) = Len(cache)
    /\ ackedLen + 1 = Len(cache)
    /\ ackedLen' = Len(cache)
    /\ ackHistory' = cache
    /\ pending' = <<>>
    /\ UNCHANGED <<
           cache, media, shadowJournal, scanPhase, scanResult, crashed,
           recovering
       >>

Crash ==
    /\ ~crashed
    /\ cache' = <<>>
    /\ ackedLen' = 0
    /\ pending' = <<>>
    /\ scanPhase' = "Idle"
    /\ scanResult' = <<>>
    /\ crashed' = TRUE
    /\ recovering' = FALSE
    /\ UNCHANGED <<media, ackHistory, shadowJournal>>

BeginScan ==
    /\ crashed
    /\ scanPhase = "Idle"
    /\ scanPhase' = "Scanning"
    /\ scanResult' = <<>>
    /\ UNCHANGED <<
           cache, media, ackedLen, ackHistory, pending, shadowJournal,
           crashed, recovering
       >>

FinishScan ==
    /\ crashed
    /\ scanPhase = "Scanning"
    /\ scanPhase' = "Scanned"
    /\ scanResult' = Parse(media)
    /\ UNCHANGED <<
           cache, media, ackedLen, ackHistory, pending, shadowJournal,
           crashed, recovering
       >>

(***************************************************************************
 * Tail removal is the remaining atomic storage primitive in this typed     *
 * model. AbortScan exposes interruption windows before and after it.        *
 ************************************************************************ ***)
TruncateTail ==
    /\ crashed
    /\ scanPhase = "Scanned"
    /\ scanResult = Parse(media)
    /\ media' = FullFrames(scanResult)
    /\ scanPhase' = "Truncated"
    /\ UNCHANGED <<
           cache, ackedLen, ackHistory, pending, shadowJournal, scanResult,
           crashed, recovering
       >>

AbortScan ==
    /\ crashed
    /\ scanPhase \in {"Scanning", "Scanned", "Truncated"}
    /\ scanPhase' = "Idle"
    /\ scanResult' = <<>>
    /\ UNCHANGED <<
           cache, media, ackedLen, ackHistory, pending, shadowJournal,
           crashed, recovering
       >>

BeginRecover ==
    /\ crashed
    /\ scanPhase = "Truncated"
    /\ scanResult = Parse(media)
    /\ media = FullFrames(scanResult)
    /\ cache' = scanResult
    /\ ackedLen' = Len(scanResult)
    /\ pending' = <<>>
    /\ shadowJournal' = scanResult
    /\ scanPhase' = "Idle"
    /\ scanResult' = <<>>
    /\ crashed' = FALSE
    /\ recovering' = TRUE
    /\ UNCHANGED <<media, ackHistory>>

FinishRecover ==
    /\ recovering
    /\ pending = <<>>
    /\ cache = shadowJournal
    /\ shadowJournal = Parse(media)
    /\ ackedLen = Len(cache)
    /\ NoTornFrame
    /\ recovering' = FALSE
    /\ UNCHANGED <<
           cache, media, ackedLen, ackHistory, pending, shadowJournal,
           scanPhase, scanResult, crashed
       >>

Init ==
    /\ cache = <<>>
    /\ media = <<>>
    /\ ackedLen = 0
    /\ ackHistory = <<>>
    /\ pending = <<>>
    /\ shadowJournal = <<>>
    /\ scanPhase = "Idle"
    /\ scanResult = <<>>
    /\ crashed = FALSE
    /\ recovering = FALSE

Next ==
    \/ \E rec \in Journal!JournalRecordUniverse : Stage(rec)
    \/ WriteFull
    \/ WriteTorn
    \/ FinishTorn
    \/ FlushAck
    \/ Crash
    \/ BeginScan
    \/ FinishScan
    \/ TruncateTail
    \/ AbortScan
    \/ BeginRecover
    \/ FinishRecover

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Physical representation and refinement invariants.                       *
 ************************************************************************ ***)

TypeOK ==
    /\ cache \in Seq(Journal!JournalRecordUniverse)
    /\ media \in Seq(FrameUniverse)
    /\ ackedLen \in 0..MaxJournalLength
    /\ ackHistory \in Seq(Journal!JournalRecordUniverse)
    /\ pending \in Seq(Journal!JournalRecordUniverse)
    /\ Len(pending) <= 1
    /\ shadowJournal \in Seq(Journal!JournalRecordUniverse)
    /\ scanPhase \in ScanPhases
    /\ scanResult \in Seq(Journal!JournalRecordUniverse)
    /\ crashed \in BOOLEAN
    /\ recovering \in BOOLEAN
    /\ Len(cache) <= MaxJournalLength
    /\ Len(media) <= MaxJournalLength
    /\ Len(shadowJournal) <= MaxJournalLength
    /\ Len(ackHistory) <= MaxJournalLength
    /\ Len(scanResult) <= MaxJournalLength

SequentialLSNs ==
    \A i \in 1..Len(media) : FrameLSN(media[i]) = i

TornTailOnly ==
    \A i \in 1..Len(media) :
        FrameKind(media[i]) = "Torn" => i = Len(media)

ShadowMatchesParse == shadowJournal = Parse(media)

PendingShape ==
    /\ (Len(pending) = 0 => ackedLen = Len(cache))
    /\ (Len(pending) = 1 =>
           /\ Len(cache) = ackedLen + 1
           /\ pending[1] = cache[Len(cache)])

AckedPrefixDurable ==
    /\ ackedLen <= Len(Parse(media))
    /\ Prefix(cache, ackedLen) = Prefix(Parse(media), ackedLen)

AcknowledgedHistoryDurable == IsPrefix(ackHistory, Parse(media))

CacheMediaCorrespondence ==
    IF crashed
    THEN /\ cache = <<>>
         /\ ackedLen = 0
         /\ pending = <<>>
    ELSE /\ IsPrefix(Parse(media), cache)
         /\ Len(cache) - Len(Parse(media)) \in 0..1
         /\ \A i \in 1..Len(media) :
                FrameRecord(media[i]) = cache[i]

RecoveryShape ==
    ~(crashed /\ recovering)

RecoveryScanShape ==
    /\ (~crashed => scanPhase = "Idle")
    /\ (scanPhase # "Idle" => crashed /\ ~recovering)
    /\ (scanPhase \in {"Idle", "Scanning"} => scanResult = <<>>)
    /\ (scanPhase \in {"Scanned", "Truncated"} =>
           scanResult = Parse(media))
    /\ (scanPhase = "Truncated" =>
           /\ NoTornFrame
           /\ media = FullFrames(scanResult))

FullMediaCanonical ==
    NoTornFrame => media = FullFrames(Parse(media))

ParsedJournalSafety == Journal!JournalSafety

WALSafety ==
    /\ TypeOK
    /\ SequentialLSNs
    /\ TornTailOnly
    /\ ShadowMatchesParse
    /\ PendingShape
    /\ AckedPrefixDurable
    /\ AcknowledgedHistoryDurable
    /\ CacheMediaCorrespondence
    /\ RecoveryShape
    /\ RecoveryScanShape
    /\ FullMediaCanonical
    /\ ParsedJournalSafety

(***************************************************************************
 * TLC checks this temporal property under Spec. Complete-frame writes map  *
 * to one Journal.Next step; all other physical actions stutter on the       *
 * substituted journal variable.                                            *
 ************************************************************************ ***)

JournalRefinement == Journal!Spec

====
