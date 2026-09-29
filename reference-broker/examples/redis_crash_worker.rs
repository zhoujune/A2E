//! Linux process-crash experiment; the controller kills this worker with SIGKILL.
use proveai_reference_broker::{
    Adapter, AppendGate, Broker, BrokerConfig, CapabilityId, CapabilitySpec, Delivery, Digest,
    GateError, Invocation, JournalRecord, Observation, RequestId, RequestSpec, RetryClass,
    TerminalResult, Value,
};
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;

fn event(message: &str) {
    println!("{message}");
    std::io::stdout().flush().unwrap();
}
fn barrier(message: &str) {
    event(message);
    let mut line = String::new();
    assert!(std::io::stdin().read_line(&mut line).unwrap() > 0, "controller disconnected");
    assert_eq!(line.trim(), "continue");
}
fn command(stream: &mut BufReader<UnixStream>, args: &[&str]) -> String {
    let mut wire = format!("*{}\r\n", args.len());
    for arg in args {
        wire.push('$');
        wire.push_str(&format!("{}\r\n{}\r\n", arg.len(), arg));
    }
    stream.get_mut().write_all(wire.as_bytes()).unwrap();
    let mut response = String::new();
    assert!(stream.read_line(&mut response).unwrap() > 0, "missing Redis response");
    response.trim_end().to_owned()
}
struct RedisAdapter { socket: PathBuf, before_send: bool, calls: usize }
impl Adapter for RedisAdapter {
    fn retry_class(&self) -> RetryClass { RetryClass::Idempotent }
    fn invoke(&mut self, invocation: Invocation) -> Delivery {
        self.calls += 1;
        event(&format!("CALL|{}", invocation.attempt));
        if self.before_send { barrier("BEFORE_SEND"); }
        let mut stream = BufReader::new(UnixStream::connect(&self.socket).unwrap());
        assert_eq!(command(&mut stream, &["AUTH", "study", "experiment-only"]), "+OK");
        let reply = command(&mut stream, &["SADD", "study:members", "member"]);
        event(&format!("REPLY|{reply}"));
        let observation = match reply.as_str() {
            // Export membership, rather than the number of new insertions.
            ":0" | ":1" => Observation::Success(Value(1)),
            r if r.starts_with("-NOPERM ") => Observation::Failure,
            _ => panic!("unexpected service response: {reply}"),
        };
        Delivery { invocation: invocation.id, observation }
    }
}
// This observer records evidence and pauses before terminal persistence.
// It performs no verified-kernel validation and never changes decisions.
struct Observer { records: Vec<JournalRecord>, prefix: PathBuf }
impl AppendGate for Observer {
    fn preview(&mut self, record: JournalRecord) -> Result<(), GateError> {
        let decision = match record {
            JournalRecord::Commit { .. } => Some("Commit"),
            JournalRecord::Fail { .. } => Some("Fail"),
            JournalRecord::Unknown { .. } => Some("Unknown"),
            _ => None,
        };
        if let Some(decision) = decision {
            std::fs::write(&self.prefix, format!("{:#?}\n", self.records)).unwrap();
            barrier(&format!("PRE_TERMINAL|{decision}"));
        }
        Ok(())
    }
    fn commit_after_wal(&mut self, record: JournalRecord, _lsn: u64) -> Result<(), GateError> {
        self.records.push(record);
        Ok(())
    }
    fn replay(&mut self, record: JournalRecord, lsn: u64) -> Result<(), GateError> {
        self.commit_after_wal(record, lsn)
    }
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 4, "usage: worker CASE_DIR SOCKET MODE");
    let directory = PathBuf::from(&args[1]);
    let mode = &args[3];
    let config = BrokerConfig {
        capabilities: vec![CapabilitySpec { id: CapabilityId(7), budget: 1 }],
        admission_manifest: None,
    };
    let observer = Observer { records: Vec::new(), prefix: directory.join("preterminal.txt") };
    let mut broker = Broker::open_with_gate(directory.join("broker.wal"), config, observer).unwrap();
    let request = if mode == "fresh" || mode == "before_send" {
        let spec = RequestSpec::idempotent(Digest(102));
        let request = broker.admit(CapabilityId(7), spec.digest).unwrap();
        broker.prepare(request, spec).unwrap();
        request
    } else { RequestId(1) };
    let mut adapter = RedisAdapter {
        socket: PathBuf::from(&args[2]), before_send: mode == "before_send", calls: 0,
    };
    let terminal = broker.run(request, 3, &mut adapter).unwrap();
    let label = match terminal {
        TerminalResult::Committed { .. } => "Commit",
        TerminalResult::Failed { .. } => "Fail",
        TerminalResult::Unknown { .. } => "Unknown",
    };
    event(&format!("TERMINAL|{label}|{}", adapter.calls));
    std::fs::write(directory.join("final-records.txt"), format!("{:#?}\n", broker.wal_records())).unwrap();
}
