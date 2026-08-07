use proveai_reference_broker::evaluation::run_evaluation;

#[test]
fn one_request_evaluation_has_exact_safety_and_accounting() {
    let report = run_evaluation(1).expect("run evaluation smoke test");
    assert!(report.rq1.all_passed);
    assert!(report.rq1.stale_delivery_rejected);
    assert_eq!(report.rq1.cases.len(), 21);
    assert!(report.rq1.cases.iter().all(|case| {
        case.passed
            && case.terminal_records == 1
            && case.authorization_ancestry
            && case.retry_bound_respected
            && case.effect_oracle_satisfied
    }));

    assert_eq!(report.rq2.mediated.requests, 1);
    assert_eq!(report.rq2.mediated.flushes, 6);
    assert_eq!(report.rq2.mediated.physical_invocations, 1);
    assert_eq!(report.rq2.mediated.abstract_effects, 1);
    assert_eq!(report.rq2.direct.flushes, 0);
    assert_eq!(report.rq2.journaled_at_least_once.flushes, 2);

    assert_eq!(report.rq2.retry_scenarios.len(), 3);
    for retry in &report.rq2.retry_scenarios {
        assert_eq!(retry.requests, 1);
        assert_eq!(retry.physical_invocations, 2);
        assert_eq!(retry.extra_invocations, 1);
    }
    assert_eq!(report.rq2.retry_scenarios[0].abstract_effects, 1);
    assert_eq!(report.rq2.retry_scenarios[0].extra_effects, 0);
    assert_eq!(report.rq2.retry_scenarios[1].abstract_effects, 1);
    assert_eq!(report.rq2.retry_scenarios[1].extra_effects, 0);
    assert_eq!(report.rq2.retry_scenarios[2].abstract_effects, 2);
    assert_eq!(report.rq2.retry_scenarios[2].extra_effects, 1);

    let json = report.to_json_pretty();
    assert!(json.starts_with("{\n  \"schema_version\": 1,"));
    assert!(json.contains("\"case_count\": 21"));
    assert!(json.ends_with("}\n"));
}
