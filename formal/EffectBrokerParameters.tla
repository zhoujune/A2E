---- MODULE EffectBrokerParameters ----
EXTENDS Naturals, FiniteSets

(***************************************************************************
 * Shared, parameterized policy surface for the Effect Broker models.      *
 *                                                                         *
 * RequestCap and InitialBudget are operator constants: the safety models  *
 * quantify over any total request-to-capability map and any per-capability *
 * natural-number budget. The operators below them are bounded TLC model   *
 * instantiations selected explicitly from .cfg files; they are not part of *
 * the abstract policy semantics.                                          *
 ************************************************************************ ***)

CONSTANTS
    Requests,
    Caps,
    BaseScopeMatched,
    ResourceScopeMatched,
    ArgumentConstraintMatched,
    ReadOnlyRequests,
    IdempotentRequests,
    DeduplicatedRequests,
    UncontrolledRequests,
    Results,
    AllowedResults,
    RequestCap(_),
    InitialBudget(_),
    MaxAttempts

CommonParametersOK ==
    /\ Requests # {}
    /\ Caps # {}
    /\ BaseScopeMatched \subseteq Requests
    /\ ResourceScopeMatched \subseteq Requests
    /\ ArgumentConstraintMatched \subseteq Requests
    /\ ReadOnlyRequests \subseteq Requests
    /\ IdempotentRequests \subseteq Requests
    /\ DeduplicatedRequests \subseteq Requests
    /\ UncontrolledRequests \subseteq Requests
    /\ ReadOnlyRequests \union IdempotentRequests
           \union DeduplicatedRequests \union UncontrolledRequests = Requests
    /\ ReadOnlyRequests \cap IdempotentRequests = {}
    /\ ReadOnlyRequests \cap DeduplicatedRequests = {}
    /\ ReadOnlyRequests \cap UncontrolledRequests = {}
    /\ IdempotentRequests \cap DeduplicatedRequests = {}
    /\ IdempotentRequests \cap UncontrolledRequests = {}
    /\ DeduplicatedRequests \cap UncontrolledRequests = {}
    /\ Results # {}
    /\ AllowedResults \subseteq Results
    /\ AllowedResults # {}
    /\ \A r \in Requests : RequestCap(r) \in Caps
    /\ \A c \in Caps : InitialBudget(c) \in Nat
    /\ MaxAttempts \in Nat \ {0}

(***************************************************************************
 * TLC-only operator substitutions used by the checked finite scenarios.  *
 ************************************************************************ ***)

UniformRequestCap(r) == CHOOSE c \in Caps : TRUE

InitialBudgetOne(c) == 1
InitialBudgetTwo(c) == 2

PrimaryCapability == CHOOSE c \in Caps : TRUE

SecondaryCapability == CHOOSE c \in Caps \ {PrimaryCapability} : TRUE

RetryPartitionRequestCap(r) ==
    IF r \in ReadOnlyRequests \union IdempotentRequests
    THEN PrimaryCapability
    ELSE SecondaryCapability

PartitionedInitialBudget(c) ==
    IF c = PrimaryCapability THEN 1 ELSE 2

====
