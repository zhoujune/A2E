use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use crate::model::{
    CapabilityId, DedupKey, Digest, JournalRecord, Observation, RequestId, RetryClass,
    UnknownReason, Value,
};

const MAGIC: [u8; 4] = *b"PVAI";
const FORMAT_VERSION: u8 = 1;
const HEADER_LEN: usize = 9;
const CHECKSUM_LEN: usize = 4;
const MAX_PAYLOAD_LEN: usize = 1_048_576;

#[derive(Debug)]
pub enum WalError {
    Io(io::Error),
    Poisoned,
    Corrupt { offset: u64, detail: &'static str },
    InvalidRecord(&'static str),
    RecordTooLarge(usize),
    LsnExhausted,
}

impl fmt::Display for WalError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "WAL I/O error: {error}"),
            Self::Poisoned => {
                formatter.write_str("WAL instance is poisoned; reopen it before appending")
            }
            Self::Corrupt { offset, detail } => {
                write!(formatter, "corrupt WAL frame at byte {offset}: {detail}")
            }
            Self::InvalidRecord(detail) => write!(formatter, "invalid WAL record: {detail}"),
            Self::RecordTooLarge(size) => {
                write!(formatter, "WAL record is too large: {size} bytes")
            }
            Self::LsnExhausted => formatter.write_str("one-based WAL LSN space exhausted"),
        }
    }
}

impl std::error::Error for WalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for WalError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RecoveryReport {
    pub records: u64,
    pub valid_bytes: u64,
    pub discarded_tail_bytes: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WalMetrics {
    pub records: u64,
    pub bytes: u64,
    pub flushes: u64,
}

#[derive(Debug)]
pub struct FileWal {
    path: PathBuf,
    file: File,
    records: Vec<JournalRecord>,
    metrics: WalMetrics,
    poisoned: bool,
}

impl FileWal {
    pub fn open(path: impl AsRef<Path>) -> Result<(Self, RecoveryReport), WalError> {
        let path = path.as_ref().to_path_buf();
        let mut file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&path)?;
        let (records, report) = recover_file(&mut file)?;
        let metrics = WalMetrics {
            records: report.records,
            bytes: report.valid_bytes,
            flushes: 0,
        };
        Ok((
            Self {
                path,
                file,
                records,
                metrics,
                poisoned: false,
            },
            report,
        ))
    }

    #[must_use]
    pub fn records(&self) -> &[JournalRecord] {
        &self.records
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub const fn metrics(&self) -> WalMetrics {
        self.metrics
    }

    pub fn append(&mut self, record: JournalRecord) -> Result<u64, WalError> {
        if self.poisoned {
            return Err(WalError::Poisoned);
        }
        let lsn = u64::try_from(self.records.len())
            .ok()
            .and_then(|length| length.checked_add(1))
            .ok_or(WalError::LsnExhausted)?;
        let frame = encode_frame(record)?;
        let frame_bytes = u64::try_from(frame.len()).map_err(|_| WalError::LsnExhausted)?;
        let next_bytes = self
            .metrics
            .bytes
            .checked_add(frame_bytes)
            .ok_or(WalError::LsnExhausted)?;
        if let Err(error) = self.file.seek(SeekFrom::End(0)) {
            self.poisoned = true;
            return Err(error.into());
        }
        if let Err(error) = self.file.write_all(&frame) {
            self.poisoned = true;
            return Err(error.into());
        }
        if let Err(error) = self.file.flush() {
            self.poisoned = true;
            return Err(error.into());
        }
        if let Err(error) = self.file.sync_data() {
            self.poisoned = true;
            return Err(error.into());
        }
        self.records.push(record);
        self.metrics.records = lsn;
        self.metrics.bytes = next_bytes;
        self.metrics.flushes = self.metrics.flushes.saturating_add(1);
        Ok(lsn)
    }

    /// Writes a prefix of a valid frame without registering a record.
    ///
    /// This is intentionally exposed only as a deterministic artifact fault
    /// hook. Reopening the WAL must discard this uncommitted tail.
    pub fn append_torn_frame(
        &mut self,
        record: JournalRecord,
        retained_bytes: usize,
    ) -> Result<usize, WalError> {
        if self.poisoned {
            return Err(WalError::Poisoned);
        }
        let frame = encode_frame(record)?;
        if retained_bytes >= frame.len() {
            return Err(WalError::InvalidRecord(
                "a torn frame must omit at least one byte",
            ));
        }
        if let Err(error) = self.file.seek(SeekFrom::End(0)) {
            self.poisoned = true;
            return Err(error.into());
        }
        if let Err(error) = self.file.write_all(&frame[..retained_bytes]) {
            self.poisoned = true;
            return Err(error.into());
        }
        if let Err(error) = self.file.flush() {
            self.poisoned = true;
            return Err(error.into());
        }
        if let Err(error) = self.file.sync_data() {
            self.poisoned = true;
            return Err(error.into());
        }
        self.poisoned = true;
        Ok(frame.len())
    }
}

fn recover_file(file: &mut File) -> Result<(Vec<JournalRecord>, RecoveryReport), WalError> {
    file.seek(SeekFrom::Start(0))?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;

    let mut records = Vec::new();
    let mut offset = 0usize;
    while offset < bytes.len() {
        let remaining = bytes.len() - offset;
        if remaining < HEADER_LEN {
            break;
        }
        if bytes[offset..offset + 4] != MAGIC {
            return Err(WalError::Corrupt {
                offset: as_u64(offset)?,
                detail: "bad frame magic",
            });
        }
        if bytes[offset + 4] != FORMAT_VERSION {
            return Err(WalError::Corrupt {
                offset: as_u64(offset)?,
                detail: "unsupported frame version",
            });
        }
        let payload_len = u32::from_le_bytes(
            bytes[offset + 5..offset + HEADER_LEN]
                .try_into()
                .expect("four-byte payload length"),
        ) as usize;
        if payload_len > MAX_PAYLOAD_LEN {
            return Err(WalError::Corrupt {
                offset: as_u64(offset)?,
                detail: "payload length exceeds limit",
            });
        }
        let Some(frame_len) = HEADER_LEN
            .checked_add(payload_len)
            .and_then(|length| length.checked_add(CHECKSUM_LEN))
        else {
            return Err(WalError::Corrupt {
                offset: as_u64(offset)?,
                detail: "frame length overflow",
            });
        };
        let Some(frame_end) = offset.checked_add(frame_len) else {
            return Err(WalError::Corrupt {
                offset: as_u64(offset)?,
                detail: "frame end overflow",
            });
        };
        if frame_end > bytes.len() {
            break;
        }

        let payload_start = offset + HEADER_LEN;
        let payload_end = payload_start + payload_len;
        let expected = u32::from_le_bytes(
            bytes[payload_end..frame_end]
                .try_into()
                .expect("four-byte checksum"),
        );
        let actual = crc32(&bytes[offset..payload_end]);
        if actual != expected {
            if frame_end == bytes.len() {
                break;
            }
            return Err(WalError::Corrupt {
                offset: as_u64(offset)?,
                detail: "checksum mismatch before final frame",
            });
        }
        let record = decode_record(&bytes[payload_start..payload_end]).map_err(|detail| {
            WalError::Corrupt {
                offset: as_u64(offset).unwrap_or(u64::MAX),
                detail,
            }
        })?;
        records.push(record);
        offset = frame_end;
    }

    let discarded = bytes.len() - offset;
    if discarded > 0 {
        file.set_len(as_u64(offset)?)?;
        file.sync_all()?;
    }
    file.seek(SeekFrom::End(0))?;
    let record_count = as_u64(records.len())?;
    Ok((
        records,
        RecoveryReport {
            records: record_count,
            valid_bytes: as_u64(offset)?,
            discarded_tail_bytes: as_u64(discarded)?,
        },
    ))
}

fn as_u64(value: usize) -> Result<u64, WalError> {
    u64::try_from(value).map_err(|_| WalError::LsnExhausted)
}

fn encode_frame(record: JournalRecord) -> Result<Vec<u8>, WalError> {
    let payload = encode_record(record);
    if payload.len() > MAX_PAYLOAD_LEN {
        return Err(WalError::RecordTooLarge(payload.len()));
    }
    let payload_len =
        u32::try_from(payload.len()).map_err(|_| WalError::RecordTooLarge(payload.len()))?;
    let mut frame = Vec::with_capacity(HEADER_LEN + payload.len() + CHECKSUM_LEN);
    frame.extend_from_slice(&MAGIC);
    frame.push(FORMAT_VERSION);
    frame.extend_from_slice(&payload_len.to_le_bytes());
    frame.extend_from_slice(&payload);
    let checksum = crc32(&frame);
    frame.extend_from_slice(&checksum.to_le_bytes());
    Ok(frame)
}

fn encode_record(record: JournalRecord) -> Vec<u8> {
    let mut output = Vec::with_capacity(80);
    match record {
        JournalRecord::Authorize {
            request,
            capability,
            digest,
        } => {
            output.push(0);
            put_u64(&mut output, request.0);
            put_u64(&mut output, capability.0);
            put_u64(&mut output, digest.0);
        }
        JournalRecord::Revoke { capability } => {
            output.push(1);
            put_u64(&mut output, capability.0);
        }
        JournalRecord::Prepare {
            request,
            class,
            digest,
            key,
            auth_ref,
        } => {
            output.push(2);
            put_u64(&mut output, request.0);
            put_retry_class(&mut output, class);
            put_u64(&mut output, digest.0);
            put_key(&mut output, key);
            put_u64(&mut output, auth_ref);
        }
        JournalRecord::Arm {
            request,
            digest,
            key,
            prepare_ref,
        } => {
            output.push(3);
            put_u64(&mut output, request.0);
            put_u64(&mut output, digest.0);
            put_key(&mut output, key);
            put_u64(&mut output, prepare_ref);
        }
        JournalRecord::Start {
            request,
            attempt,
            digest,
            key,
            arm_ref,
        } => {
            output.push(4);
            put_u64(&mut output, request.0);
            put_u64(&mut output, attempt);
            put_u64(&mut output, digest.0);
            put_key(&mut output, key);
            put_u64(&mut output, arm_ref);
        }
        JournalRecord::Outcome {
            request,
            attempt,
            observation,
            digest,
            key,
            start_ref,
        } => {
            output.push(5);
            put_u64(&mut output, request.0);
            put_u64(&mut output, attempt);
            put_observation(&mut output, observation);
            put_u64(&mut output, digest.0);
            put_key(&mut output, key);
            put_u64(&mut output, start_ref);
        }
        JournalRecord::Commit {
            request,
            attempt,
            value,
            digest,
            key,
            outcome_ref,
        } => {
            output.push(6);
            put_u64(&mut output, request.0);
            put_u64(&mut output, attempt);
            put_u64(&mut output, value.0);
            put_u64(&mut output, digest.0);
            put_key(&mut output, key);
            put_u64(&mut output, outcome_ref);
        }
        JournalRecord::Fail {
            request,
            attempt,
            digest,
            key,
            outcome_ref,
        } => {
            output.push(7);
            put_u64(&mut output, request.0);
            put_u64(&mut output, attempt);
            put_u64(&mut output, digest.0);
            put_key(&mut output, key);
            put_u64(&mut output, outcome_ref);
        }
        JournalRecord::Unknown {
            request,
            attempt,
            reason,
            digest,
            key,
            evidence_ref,
        } => {
            output.push(8);
            put_u64(&mut output, request.0);
            put_optional_u64(&mut output, attempt);
            put_unknown_reason(&mut output, reason);
            put_u64(&mut output, digest.0);
            put_key(&mut output, key);
            put_u64(&mut output, evidence_ref);
        }
    }
    output
}

fn decode_record(bytes: &[u8]) -> Result<JournalRecord, &'static str> {
    let mut reader = Reader::new(bytes);
    let record = match reader.byte()? {
        0 => JournalRecord::Authorize {
            request: RequestId(reader.u64()?),
            capability: CapabilityId(reader.u64()?),
            digest: Digest(reader.u64()?),
        },
        1 => JournalRecord::Revoke {
            capability: CapabilityId(reader.u64()?),
        },
        2 => JournalRecord::Prepare {
            request: RequestId(reader.u64()?),
            class: reader.retry_class()?,
            digest: Digest(reader.u64()?),
            key: reader.key()?,
            auth_ref: reader.u64()?,
        },
        3 => JournalRecord::Arm {
            request: RequestId(reader.u64()?),
            digest: Digest(reader.u64()?),
            key: reader.key()?,
            prepare_ref: reader.u64()?,
        },
        4 => JournalRecord::Start {
            request: RequestId(reader.u64()?),
            attempt: reader.u64()?,
            digest: Digest(reader.u64()?),
            key: reader.key()?,
            arm_ref: reader.u64()?,
        },
        5 => JournalRecord::Outcome {
            request: RequestId(reader.u64()?),
            attempt: reader.u64()?,
            observation: reader.observation()?,
            digest: Digest(reader.u64()?),
            key: reader.key()?,
            start_ref: reader.u64()?,
        },
        6 => JournalRecord::Commit {
            request: RequestId(reader.u64()?),
            attempt: reader.u64()?,
            value: Value(reader.u64()?),
            digest: Digest(reader.u64()?),
            key: reader.key()?,
            outcome_ref: reader.u64()?,
        },
        7 => JournalRecord::Fail {
            request: RequestId(reader.u64()?),
            attempt: reader.u64()?,
            digest: Digest(reader.u64()?),
            key: reader.key()?,
            outcome_ref: reader.u64()?,
        },
        8 => {
            let request = RequestId(reader.u64()?);
            let attempt = reader.optional_u64()?;
            JournalRecord::Unknown {
                request,
                attempt,
                reason: reader.unknown_reason()?,
                digest: Digest(reader.u64()?),
                key: reader.key()?,
                evidence_ref: reader.u64()?,
            }
        }
        _ => return Err("unknown record tag"),
    };
    if reader.finished() {
        Ok(record)
    } else {
        Err("trailing bytes in record")
    }
}

fn put_u64(output: &mut Vec<u8>, value: u64) {
    output.extend_from_slice(&value.to_le_bytes());
}

fn put_optional_u64(output: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            output.push(1);
            put_u64(output, value);
        }
        None => output.push(0),
    }
}

fn put_key(output: &mut Vec<u8>, key: Option<DedupKey>) {
    put_optional_u64(output, key.map(|key| key.0));
}

fn put_retry_class(output: &mut Vec<u8>, class: RetryClass) {
    output.push(match class {
        RetryClass::ReadOnly => 0,
        RetryClass::Idempotent => 1,
        RetryClass::Deduplicated => 2,
        RetryClass::Uncontrolled => 3,
    });
}

fn put_observation(output: &mut Vec<u8>, observation: Observation) {
    match observation {
        Observation::Success(value) => {
            output.push(0);
            put_u64(output, value.0);
        }
        Observation::Failure => output.push(1),
        Observation::Ambiguous => output.push(2),
        Observation::InvalidResult(value) => {
            output.push(3);
            put_u64(output, value.0);
        }
    }
}

fn put_unknown_reason(output: &mut Vec<u8>, reason: UnknownReason) {
    output.push(match reason {
        UnknownReason::Exhausted => 0,
        UnknownReason::Recovery => 1,
        UnknownReason::NonConclusiveFailure => 2,
        UnknownReason::AmbiguousOutcome => 3,
        UnknownReason::InvalidResult => 4,
    });
}

struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Reader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn byte(&mut self) -> Result<u8, &'static str> {
        let value = *self.bytes.get(self.position).ok_or("truncated record")?;
        self.position += 1;
        Ok(value)
    }

    fn u64(&mut self) -> Result<u64, &'static str> {
        let end = self
            .position
            .checked_add(8)
            .ok_or("record length overflow")?;
        let bytes = self.bytes.get(self.position..end).ok_or("truncated u64")?;
        self.position = end;
        Ok(u64::from_le_bytes(
            bytes.try_into().expect("eight-byte integer"),
        ))
    }

    fn optional_u64(&mut self) -> Result<Option<u64>, &'static str> {
        match self.byte()? {
            0 => Ok(None),
            1 => Ok(Some(self.u64()?)),
            _ => Err("invalid option tag"),
        }
    }

    fn key(&mut self) -> Result<Option<DedupKey>, &'static str> {
        self.optional_u64().map(|key| key.map(DedupKey))
    }

    fn retry_class(&mut self) -> Result<RetryClass, &'static str> {
        match self.byte()? {
            0 => Ok(RetryClass::ReadOnly),
            1 => Ok(RetryClass::Idempotent),
            2 => Ok(RetryClass::Deduplicated),
            3 => Ok(RetryClass::Uncontrolled),
            _ => Err("invalid retry-class tag"),
        }
    }

    fn observation(&mut self) -> Result<Observation, &'static str> {
        match self.byte()? {
            0 => Ok(Observation::Success(Value(self.u64()?))),
            1 => Ok(Observation::Failure),
            2 => Ok(Observation::Ambiguous),
            3 => Ok(Observation::InvalidResult(Value(self.u64()?))),
            _ => Err("invalid observation tag"),
        }
    }

    fn unknown_reason(&mut self) -> Result<UnknownReason, &'static str> {
        match self.byte()? {
            0 => Ok(UnknownReason::Exhausted),
            1 => Ok(UnknownReason::Recovery),
            2 => Ok(UnknownReason::NonConclusiveFailure),
            3 => Ok(UnknownReason::AmbiguousOutcome),
            4 => Ok(UnknownReason::InvalidResult),
            _ => Err("invalid unknown-reason tag"),
        }
    }

    fn finished(&self) -> bool {
        self.position == self.bytes.len()
    }
}

fn crc32(bytes: &[u8]) -> u32 {
    let mut crc = u32::MAX;
    for byte in bytes {
        crc ^= u32::from(*byte);
        for _ in 0..8 {
            let mask = 0u32.wrapping_sub(crc & 1);
            crc = (crc >> 1) ^ (0xedb8_8320 & mask);
        }
    }
    !crc
}
