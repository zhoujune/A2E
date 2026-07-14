use vstd::prelude::*;

#[path = "t1_global_projections.rs"]
pub mod projection_layer;

verus! {

use projection_layer::global_layer;
use global_layer::bridge_layer;
use bridge_layer::contract_layer;
use contract_layer::p3_layer::p2_layer::p1_layer::p0_layer;
use p0_layer::config_layer;

// G1-E gives the paper machine its relational execution semantics.  The
// carried configurations are authoritative: `exec` is not defined by the
// functional `p0_layer::run`.  Correspondence with that already verified
// functional presentation is proved below.

pub struct BrokerExecution {
    pub configs: Seq<p0_layer::State>,
    pub events: Seq<global_layer::GlobalEvent>,
}

pub open spec fn broker_init(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
) -> bool {
    state == p0_layer::initial_state(cfg)
}

pub open spec fn broker_step(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
) -> bool {
    match global_layer::broker_decode(event) {
        Option::None => false,
        Option::Some(local) => p0_layer::physical_step(
            cfg, before, local, after,
        ),
    }
}

pub open spec fn exec(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
) -> bool {
    execution.configs.len() == execution.events.len() + 1
        && broker_init(cfg, execution.configs[0])
        && forall|index: nat| index < execution.events.len() ==>
            #[trigger] broker_step(
                cfg,
                execution.configs[index as int],
                execution.events[index as int],
                execution.configs[(index + 1) as int],
            )
}

pub open spec fn execs(
    cfg: config_layer::FullConfig,
) -> ISet<BrokerExecution> {
    ISet::new(|execution: BrokerExecution| exec(cfg, execution))
}

pub open spec fn execution_prefix(
    execution: BrokerExecution,
    length: nat,
) -> BrokerExecution {
    BrokerExecution {
        configs: execution.configs.take((length + 1) as int),
        events: execution.events.take(length as int),
    }
}

pub proof fn broker_initial_is_exact(
    cfg: config_layer::FullConfig,
    state: p0_layer::State,
)
    ensures
        broker_init(cfg, state) <==> state == p0_layer::initial_state(cfg),
{
}

pub proof fn broker_step_decodes(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires broker_step(cfg, before, event, after),
    ensures exists|local: p0_layer::Event| #![auto]
        global_layer::broker_decode(event) == Option::Some(local)
            && p0_layer::physical_step(cfg, before, local, after),
{
    match global_layer::broker_decode(event) {
        Option::None => {},
        Option::Some(local) => {
            assert(global_layer::broker_decode(event) == Option::Some(local));
        },
    }
}

pub proof fn broker_step_rejects_backend_only(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires global_layer::backend_only_constructor(event),
    ensures !broker_step(cfg, before, event, after),
{
    global_layer::broker_decode_rejects_backend_only(event);
}

pub proof fn broker_step_closure(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires broker_step(cfg, before, event, after),
    ensures
        global_layer::broker_constructor(event),
        !global_layer::backend_only_constructor(event),
{
    global_layer::broker_decode_accepts_exactly(event);
    global_layer::broker_constructor_partition(event);
}

pub proof fn exec_rejects_backend_only_at(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
    index: nat,
)
    requires
        exec(cfg, execution),
        index < execution.events.len(),
        global_layer::backend_only_constructor(
            execution.events[index as int],
        ),
    ensures false,
{
    assert(broker_step(
        cfg,
        execution.configs[index as int],
        execution.events[index as int],
        execution.configs[(index + 1) as int],
    ));
    broker_step_rejects_backend_only(
        cfg,
        execution.configs[index as int],
        execution.events[index as int],
        execution.configs[(index + 1) as int],
    );
}

pub proof fn broker_step_is_local_apply(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    local: p0_layer::Event,
    after: p0_layer::State,
)
    requires
        broker_step(cfg, before, event, after),
        global_layer::broker_decode(event) == Option::Some(local),
    ensures
        p0_layer::admissibly_enabled(cfg, before, local),
        after == p0_layer::apply(cfg, before, local),
{
}

pub proof fn exec_is_member(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
)
    ensures execs(cfg).contains(execution) <==> exec(cfg, execution),
{
}

pub proof fn exec_prefix(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
    length: nat,
)
    requires
        exec(cfg, execution),
        length <= execution.events.len(),
    ensures exec(cfg, execution_prefix(execution, length)),
{
    let prefix = execution_prefix(execution, length);
    assert(prefix.events.len() == length);
    assert(prefix.configs.len() == length + 1);
    assert(prefix.configs[0] == execution.configs[0]);
    assert forall|index: nat| index < prefix.events.len() implies
        #[trigger] broker_step(
            cfg,
            prefix.configs[index as int],
            prefix.events[index as int],
            prefix.configs[(index + 1) as int],
        ) by {
        assert(index < execution.events.len());
        assert(index + 1 < execution.configs.len());
        assert(prefix.events[index as int]
            == execution.events[index as int]);
        assert(prefix.configs[index as int]
            == execution.configs[index as int]);
        assert(prefix.configs[(index + 1) as int]
            == execution.configs[(index + 1) as int]);
    }
}

pub proof fn execution_prefix_idempotent(
    execution: BrokerExecution,
    outer: nat,
    inner: nat,
)
    requires
        execution.configs.len() == execution.events.len() + 1,
        inner <= outer,
        outer <= execution.events.len(),
    ensures execution_prefix(execution_prefix(execution, outer), inner)
        == execution_prefix(execution, inner),
{
    let left = execution_prefix(execution_prefix(execution, outer), inner);
    let right = execution_prefix(execution, inner);
    assert(left.events =~= right.events);
    assert(left.configs.len() == inner + 1);
    assert(right.configs.len() == inner + 1);
    assert forall|index: int| 0 <= index < left.configs.len() implies
        left.configs[index] == right.configs[index] by {
        assert(index < inner + 1);
        assert(index < outer + 1);
        assert(index < execution.configs.len());
    }
    assert(left.configs =~= right.configs);
    assert(left == right);
}

pub proof fn exec_trace_closed(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
)
    requires exec(cfg, execution),
    ensures projection_layer::broker_trace_closed(execution.events),
    decreases execution.events.len(),
{
    if execution.events.len() > 0 {
        let length: nat = (execution.events.len() - 1) as nat;
        let prefix = execution_prefix(execution, length);
        exec_prefix(cfg, execution, length);
        exec_trace_closed(cfg, prefix);
        assert(prefix.events =~= execution.events.drop_last());
        assert(length < execution.events.len());
        assert(broker_step(
            cfg,
            execution.configs[length as int],
            execution.events[length as int],
            execution.configs[(length + 1) as int],
        ));
        assert(execution.events[length as int] == execution.events.last());
        broker_step_closure(
            cfg,
            execution.configs[length as int],
            execution.events.last(),
            execution.configs[(length + 1) as int],
        );
    }
}

pub proof fn every_exec_has_length_preserving_decode(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
)
    requires exec(cfg, execution),
    ensures exists|locals: Seq<p0_layer::Event>| #![auto]
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals)
            && locals.len() == execution.events.len(),
{
    exec_trace_closed(cfg, execution);
    projection_layer::broker_decode_trace_accepts_exactly(execution.events);
    match projection_layer::broker_decode_trace(execution.events) {
        Option::None => {},
        Option::Some(locals) => {
            projection_layer::broker_decode_trace_inverse(
                execution.events, locals,
            );
            assert(projection_layer::broker_decode_trace(execution.events)
                == Option::Some(locals));
        },
    }
}

pub proof fn decoded_last_event(
    globals: Seq<global_layer::GlobalEvent>,
    locals: Seq<p0_layer::Event>,
)
    requires
        projection_layer::broker_decode_trace(globals)
            == Option::Some(locals),
        globals.len() > 0,
    ensures
        locals.len() > 0,
        projection_layer::broker_decode_trace(globals.drop_last())
            == Option::Some(locals.drop_last()),
        global_layer::broker_decode(globals.last())
            == Option::Some(locals.last()),
{
    projection_layer::broker_decode_trace_inverse(globals, locals);
    let length: nat = (globals.len() - 1) as nat;
    assert(length <= globals.len());
    projection_layer::broker_decode_trace_take(globals, locals, length);
    assert(globals.take(length as int) =~= globals.drop_last());
    assert(locals.take(length as int) =~= locals.drop_last());
    projection_layer::broker_decode_trace_push(
        globals.drop_last(), globals.last(),
    );
    match global_layer::broker_decode(globals.last()) {
        Option::None => {},
        Option::Some(local) => {
            assert(Option::Some(locals.drop_last().push(local))
                == Option::Some(locals));
            assert(locals.drop_last().push(local) == locals);
            assert(local == locals.last());
        },
    }
}

// Joint induction is important here: local admissibility and state/run
// correspondence establish one another at the last step.  Neither property
// is baked into the definition of the relational execution.
pub proof fn decoded_exec_refines_local_run(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures
        p0_layer::admissibly_executable(cfg, locals),
        locals.len() == execution.events.len(),
        execution.configs.last() == p0_layer::run(cfg, locals),
    decreases execution.events.len(),
{
    projection_layer::broker_decode_trace_inverse(
        execution.events, locals,
    );
    if execution.events.len() == 0 {
        assert(locals.len() == 0);
        assert(locals =~= Seq::<p0_layer::Event>::empty());
        assert(execution.configs.len() == 1);
        assert(execution.configs.last() == execution.configs[0]);
        assert(broker_init(cfg, execution.configs[0]));
    } else {
        let length: nat = (execution.events.len() - 1) as nat;
        let prefix = execution_prefix(execution, length);
        let local_prefix = locals.drop_last();
        exec_prefix(cfg, execution, length);
        decoded_last_event(execution.events, locals);
        assert(prefix.events =~= execution.events.drop_last());
        assert(projection_layer::broker_decode_trace(prefix.events)
            == Option::Some(local_prefix));
        decoded_exec_refines_local_run(cfg, prefix, local_prefix);

        let global = execution.events.last();
        let local = locals.last();
        let before = execution.configs[length as int];
        let after = execution.configs[(length + 1) as int];
        assert(length < execution.events.len());
        assert(global == execution.events[length as int]);
        assert(broker_step(cfg, before, global, after));
        assert(global_layer::broker_decode(global) == Option::Some(local));
        broker_step_is_local_apply(cfg, before, global, local, after);

        assert(prefix.configs.len() == length + 1);
        assert(prefix.configs.last() == before);
        assert(before == p0_layer::run(cfg, local_prefix));
        assert(locals.drop_last().push(local) =~= locals);
        assert(p0_layer::run(cfg, locals)
            == p0_layer::apply(
                cfg, p0_layer::run(cfg, local_prefix), local,
            ));
        assert(execution.configs.len() == execution.events.len() + 1);
        assert(after == execution.configs.last());
    }
}

pub proof fn every_exec_decodes_to_admissible_local_trace(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
)
    requires exec(cfg, execution),
    ensures exists|locals: Seq<p0_layer::Event>| #![auto]
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals)
            && locals.len() == execution.events.len()
            && p0_layer::admissibly_executable(cfg, locals)
            && execution.configs.last() == p0_layer::run(cfg, locals),
{
    every_exec_has_length_preserving_decode(cfg, execution);
    match projection_layer::broker_decode_trace(execution.events) {
        Option::None => {},
        Option::Some(locals) => {
            decoded_exec_refines_local_run(cfg, execution, locals);
            assert(projection_layer::broker_decode_trace(execution.events)
                == Option::Some(locals));
        },
    }
}

pub proof fn exact_config_run_correspondence_at(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
    locals: Seq<p0_layer::Event>,
    index: nat,
)
    requires
        exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
        index <= execution.events.len(),
    ensures
        execution.configs[index as int]
            == p0_layer::run(cfg, locals.take(index as int)),
{
    projection_layer::broker_decode_trace_inverse(
        execution.events, locals,
    );
    let prefix = execution_prefix(execution, index);
    exec_prefix(cfg, execution, index);
    projection_layer::broker_decode_trace_take(
        execution.events, locals, index,
    );
    decoded_exec_refines_local_run(
        cfg, prefix, locals.take(index as int),
    );
    assert(prefix.configs.len() == index + 1);
    assert(prefix.configs.last() == execution.configs[index as int]);
}

pub proof fn exact_config_run_correspondence(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
    locals: Seq<p0_layer::Event>,
)
    requires
        exec(cfg, execution),
        projection_layer::broker_decode_trace(execution.events)
            == Option::Some(locals),
    ensures forall|index: nat| index <= execution.events.len() ==>
        #[trigger] execution.configs[index as int]
            == p0_layer::run(cfg, locals.take(index as int)),
{
    assert forall|index: nat| index <= execution.events.len() implies
        #[trigger] execution.configs[index as int]
            == p0_layer::run(cfg, locals.take(index as int)) by {
        exact_config_run_correspondence_at(
            cfg, execution, locals, index,
        );
    }
}

pub proof fn initial_preserves_local_inductive_invariant(
    cfg: config_layer::FullConfig,
)
    requires config_layer::full_config_wf(cfg),
    ensures contract_layer::local_inductive_invariant(
        cfg, p0_layer::initial_state(cfg),
    ),
{
    contract_layer::p3_layer::initial_p3_invariant(cfg);
    contract_layer::p3_implies_broker_contract_invariant(
        cfg, p0_layer::initial_state(cfg),
    );
}

pub proof fn broker_step_preserves_local_inductive_invariant(
    cfg: config_layer::FullConfig,
    before: p0_layer::State,
    event: global_layer::GlobalEvent,
    after: p0_layer::State,
)
    requires
        config_layer::full_config_wf(cfg),
        contract_layer::local_inductive_invariant(cfg, before),
        broker_step(cfg, before, event, after),
    ensures contract_layer::local_inductive_invariant(cfg, after),
{
    match global_layer::broker_decode(event) {
        Option::None => {},
        Option::Some(local) => {
            assert(p0_layer::physical_step(cfg, before, local, after));
            assert(p0_layer::admissibly_enabled(cfg, before, local));
            assert(after == p0_layer::apply(cfg, before, local));
            contract_layer::p3_layer::step_preserves_p3_invariant(
                cfg, before, local,
            );
            contract_layer::p3_implies_broker_contract_invariant(cfg, after);
        },
    }
}

pub proof fn every_exec_config_preserves_local_inductive_invariant(
    cfg: config_layer::FullConfig,
    execution: BrokerExecution,
)
    requires
        config_layer::full_config_wf(cfg),
        exec(cfg, execution),
    ensures forall|index: nat| index < execution.configs.len() ==>
        #[trigger] contract_layer::local_inductive_invariant(
            cfg, execution.configs[index as int],
        ),
{
    every_exec_has_length_preserving_decode(cfg, execution);
    match projection_layer::broker_decode_trace(execution.events) {
        Option::None => {},
        Option::Some(locals) => {
            decoded_exec_refines_local_run(cfg, execution, locals);
            exact_config_run_correspondence(cfg, execution, locals);
            assert forall|index: nat| index < execution.configs.len() implies
                #[trigger] contract_layer::local_inductive_invariant(
                    cfg, execution.configs[index as int],
                ) by {
                assert(index <= execution.events.len());
                p0_layer::executable_prefix(cfg, locals, index);
                contract_layer::p3_layer::executable_run_p3_invariant(
                    cfg, locals.take(index as int),
                );
                contract_layer::p3_implies_broker_contract_invariant(
                    cfg,
                    p0_layer::run(cfg, locals.take(index as int)),
                );
            }
        },
    }
}

} // verus!
