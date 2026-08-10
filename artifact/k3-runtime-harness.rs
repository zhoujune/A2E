extern crate k3_append_linearization_kernel;

use k3_append_linearization_kernel::{
    k3_initial, k3_linearize, k3_return, k3_try_call, KJournalRecord,
};

fn main() {
    let mut state = k3_initial();
    let authorize = KJournalRecord::Authorize {
        request: 1,
        capability: 1,
        digest: 1,
    };

    assert!(k3_try_call(&mut state, authorize));
    let lsn =
        k3_linearize(&mut state, authorize).expect("authorized record must linearize");
    assert_eq!(lsn, 1);
    assert_eq!(k3_return(&mut state), Some(1));
    assert_eq!(state.journal.len(), 1);
    assert_eq!(state.ack_cuts, vec![1]);

    println!("K3 proof-erased runtime smoke passed: lsn={lsn}, journal_len=1");
}
