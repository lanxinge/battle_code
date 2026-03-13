import VerseFramework.Rules.Monadic

namespace VerseFramework

def AggregateWholeSupport (ctx : RuleContext) (a : AggregateId) : Prop :=
  ctx.HasAggregateFact a .presentedAsTotalObject

def AggregateBlocker (ctx : RuleContext) (a : AggregateId) : Prop :=
  ctx.HasAggregateFact a .presentedAsFrameworkOnly

def AggregateLowerTierRealitySupport
    (ctx : RuleContext) (a : AggregateId) (tier : CountableTier) : Prop :=
  ctx.HasAggregateFact a (.membersRealizeTierObjectsAt tier)

def AggregateLowerTierIndependenceSupport
    (ctx : RuleContext) (a : AggregateId) (tier : CountableTier) : Prop :=
  ctx.HasAggregateFact a (.membersArePairwiseCausallyIndependentAt tier) ∧
  ctx.HasAggregateFact a (.membersArePairwiseDynamicallyIndependentAt tier) ∧
  ctx.HasAggregateFact a (.membersDoNotRequireExternalSupportAt tier)

def GeneratedHierarchyRealitySupport
    (ctx : RuleContext) (a : AggregateId) : Prop :=
  ctx.HasAggregateFact a .generatedHierarchyPresentedAsActualObjects

def FixedPointClosureSupport (ctx : RuleContext) (a : AggregateId) : Prop :=
  ctx.HasAggregateFact a .describesLimitClosureOfPreviousLayers ∨
  ctx.HasAggregateFact a .describesDiagonalClosure ∨
  ctx.HasAggregateFact a .describesOrdinalRecursiveGenerator

def LowerTierPeerIndependenceRequired
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) (tier : CountableTier) : Prop :=
  match standard with
  | .strict => AggregateLowerTierIndependenceSupport ctx a tier
  | .lenient => True

def FiniteOmegaPowerHierarchyIndependenceSupport
    (ctx : RuleContext) (a : AggregateId) : Prop :=
  AggregateLowerTierIndependenceSupport ctx a .omega ∧
  ∀ n : Nat, AggregateLowerTierIndependenceSupport ctx a (.omegaPowNat (n + 2))

def GeneratedHierarchyPeerIndependenceRequired
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) : Prop :=
  match standard with
  | .strict => FiniteOmegaPowerHierarchyIndependenceSupport ctx a
  | .lenient => True

def SupportsOmegaMulNatAggregate
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) (n : Nat) : Prop :=
  2 ≤ n ∧
  AggregateWholeSupport ctx a ∧
  ¬ AggregateBlocker ctx a ∧
  AggregateLowerTierRealitySupport ctx a .omega ∧
  LowerTierPeerIndependenceRequired standard ctx a .omega ∧
  ctx.HasAggregateFact a (.hasExactlyNIndependentMembersAt .omega n)

def SupportsOmegaPowTwoAggregate
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) : Prop :=
  AggregateWholeSupport ctx a ∧
  ¬ AggregateBlocker ctx a ∧
  AggregateLowerTierRealitySupport ctx a .omega ∧
  LowerTierPeerIndependenceRequired standard ctx a .omega ∧
  ctx.HasAggregateFact a (.hasCountablyManyIndependentMembersAt .omega)

def SupportsOmegaPowSuccAggregate
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) (lower : CountableTier) : Prop :=
  AggregateWholeSupport ctx a ∧
  ¬ AggregateBlocker ctx a ∧
  AggregateLowerTierRealitySupport ctx a lower ∧
  LowerTierPeerIndependenceRequired standard ctx a lower ∧
  ctx.HasAggregateFact a (.hasCountablyManyIndependentMembersAt lower)

def SupportsOmegaPowOmegaAggregate
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) : Prop :=
  AggregateWholeSupport ctx a ∧
  ¬ AggregateBlocker ctx a ∧
  GeneratedHierarchyRealitySupport ctx a ∧
  ctx.HasAggregateFact a .describesOmegaPowerSuccessorRule ∧
  ctx.HasAggregateFact a .describesAllFiniteOmegaPowerIterations ∧
  GeneratedHierarchyPeerIndependenceRequired standard ctx a

def SupportsFixedPointAggregate
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) : Prop :=
  AggregateWholeSupport ctx a ∧
  ¬ AggregateBlocker ctx a ∧
  GeneratedHierarchyRealitySupport ctx a ∧
  ctx.HasAggregateFact a .describesOmegaPowerSuccessorRule ∧
  ctx.HasAggregateFact a .describesAllFiniteOmegaPowerIterations ∧
  FixedPointClosureSupport ctx a ∧
  GeneratedHierarchyPeerIndependenceRequired standard ctx a

/--
Conservative policy:
- tiers above `omega` are never inferred from lower-tier size language alone;
- finite and countable aggregate tiers require explicit text that their lower-tier
  members are real tier objects;
- the strict standard additionally requires peer independence at the relevant
  lower tier, while the lenient standard does not;
- `omega^omega` and fixed-point tiers additionally require the recursively
  generated hierarchy itself to be recognized as an actually realized total
  object, rather than a bare rule schema;
- the strict standard also requires peer independence throughout the generated
  finite omega-power hierarchy used by `omega^omega` and fixed-point claims.
-/
def SupportsCountableTier
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (target : HierarchyTarget) :
    CountableTier → Prop
  | .omega =>
      match target with
      | .world u => IsMonadicUniverse ctx u
      | .aggregate _ => False
  | .omegaMulNat n =>
      match target with
      | .world _ => False
      | .aggregate a => SupportsOmegaMulNatAggregate standard ctx a n
  | .omegaPowNat 0 => False
  | .omegaPowNat 1 => False
  | .omegaPowNat 2 =>
      match target with
      | .world _ => False
      | .aggregate a => SupportsOmegaPowTwoAggregate standard ctx a
  | .omegaPowNat (n + 3) =>
      match target with
      | .world _ => False
      | .aggregate a => SupportsOmegaPowSuccAggregate standard ctx a (.omegaPowNat (n + 2))
  | .omegaPowOmega =>
      match target with
      | .world _ => False
      | .aggregate a => SupportsOmegaPowOmegaAggregate standard ctx a
  | .fixedPoint _ =>
      match target with
      | .world _ => False
      | .aggregate a => SupportsFixedPointAggregate standard ctx a

theorem not_supportsOmegaMulNat_of_aggregateFrameworkOnly
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hFramework : AggregateBlocker ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaMulNat n) := by
  intro h
  rcases h with ⟨_, _, hNoBlock, _, _, _⟩
  exact hNoBlock hFramework

theorem not_supportsOmegaMulNat_of_no_aggregateWholeSupport
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hNoWhole : ¬ AggregateWholeSupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaMulNat n) := by
  intro h
  rcases h with ⟨_, hWhole, _, _, _, _⟩
  exact hNoWhole hWhole

theorem not_supportsOmegaMulNat_of_missing_lowerTierReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hNoReality : ¬ AggregateLowerTierRealitySupport ctx a .omega) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaMulNat n) := by
  intro h
  rcases h with ⟨_, _, _, hReality, _, _⟩
  exact hNoReality hReality

theorem not_supportsOmegaMulNat_of_missing_lowerTierIndependence
    {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hNoIndependence : ¬ AggregateLowerTierIndependenceSupport ctx a .omega) :
    ¬ SupportsCountableTier .strict ctx (.aggregate a) (.omegaMulNat n) := by
  intro h
  rcases h with ⟨_, _, _, _, hIndependence, _⟩
  exact hNoIndependence hIndependence

theorem not_supportsOmegaPowNat_two_of_aggregateFrameworkOnly
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hFramework : AggregateBlocker ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat 2) := by
  intro h
  rcases h with ⟨_, hNoBlock, _, _, _⟩
  exact hNoBlock hFramework

theorem not_supportsOmegaPowNat_two_of_no_aggregateWholeSupport
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hNoWhole : ¬ AggregateWholeSupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat 2) := by
  intro h
  rcases h with ⟨hWhole, _, _, _, _⟩
  exact hNoWhole hWhole

theorem not_supportsOmegaPowNat_two_of_missing_lowerTierReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hNoReality : ¬ AggregateLowerTierRealitySupport ctx a .omega) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat 2) := by
  intro h
  rcases h with ⟨_, _, hReality, _, _⟩
  exact hNoReality hReality

theorem not_supportsOmegaPowNat_two_of_missing_lowerTierIndependence
    {ctx : RuleContext} {a : AggregateId}
    (hNoIndependence : ¬ AggregateLowerTierIndependenceSupport ctx a .omega) :
    ¬ SupportsCountableTier .strict ctx (.aggregate a) (.omegaPowNat 2) := by
  intro h
  rcases h with ⟨_, _, _, hIndependence, _⟩
  exact hNoIndependence hIndependence

theorem not_supportsOmegaPowNat_succ_of_aggregateFrameworkOnly
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hFramework : AggregateBlocker ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat (n + 3)) := by
  intro h
  rcases h with ⟨_, hNoBlock, _, _, _⟩
  exact hNoBlock hFramework

theorem not_supportsOmegaPowNat_succ_of_no_aggregateWholeSupport
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hNoWhole : ¬ AggregateWholeSupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat (n + 3)) := by
  intro h
  rcases h with ⟨hWhole, _, _, _, _⟩
  exact hNoWhole hWhole

theorem not_supportsOmegaPowNat_succ_of_missing_lowerTierReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hNoReality :
      ¬ AggregateLowerTierRealitySupport ctx a (.omegaPowNat (n + 2))) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat (n + 3)) := by
  intro h
  rcases h with ⟨_, _, hReality, _, _⟩
  exact hNoReality hReality

theorem not_supportsOmegaPowNat_succ_of_missing_lowerTierIndependence
    {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (hNoIndependence :
      ¬ AggregateLowerTierIndependenceSupport ctx a (.omegaPowNat (n + 2))) :
    ¬ SupportsCountableTier .strict ctx (.aggregate a) (.omegaPowNat (n + 3)) := by
  intro h
  rcases h with ⟨_, _, _, hIndependence, _⟩
  exact hNoIndependence hIndependence

theorem not_supportsOmegaPowOmega_of_aggregateFrameworkOnly
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hFramework : AggregateBlocker ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega := by
  intro h
  rcases h with ⟨_, hNoBlock, _, _, _, _⟩
  exact hNoBlock hFramework

theorem not_supportsOmegaPowOmega_of_no_aggregateWholeSupport
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hNoWhole : ¬ AggregateWholeSupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega := by
  intro h
  rcases h with ⟨hWhole, _, _, _, _, _⟩
  exact hNoWhole hWhole

theorem not_supportsOmegaPowOmega_of_missing_generatedHierarchyReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hNoReality : ¬ GeneratedHierarchyRealitySupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega := by
  intro h
  rcases h with ⟨_, _, hReality, _, _, _⟩
  exact hNoReality hReality

theorem not_supportsOmegaPowOmega_of_missing_successorRule
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hNoRule : ¬ ctx.HasAggregateFact a .describesOmegaPowerSuccessorRule) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega := by
  intro h
  rcases h with ⟨_, _, _, hRule, _, _⟩
  exact hNoRule hRule

theorem not_supportsOmegaPowOmega_of_missing_finiteIterationPermission
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (hNoFinite : ¬ ctx.HasAggregateFact a .describesAllFiniteOmegaPowerIterations) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega := by
  intro h
  rcases h with ⟨_, _, _, _, hFinite, _⟩
  exact hNoFinite hFinite

theorem not_supportsOmegaPowOmega_of_missing_generatedHierarchyIndependence
    {ctx : RuleContext} {a : AggregateId}
    (hNoIndependence : ¬ FiniteOmegaPowerHierarchyIndependenceSupport ctx a) :
    ¬ SupportsCountableTier .strict ctx (.aggregate a) .omegaPowOmega := by
  intro h
  rcases h with ⟨_, _, _, _, _, hIndependence⟩
  exact hNoIndependence hIndependence

theorem not_supportsFixedPoint_of_aggregateFrameworkOnly
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {label : String}
    (hFramework : AggregateBlocker ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.fixedPoint label) := by
  intro h
  rcases h with ⟨_, hNoBlock, _, _, _, _, _⟩
  exact hNoBlock hFramework

theorem not_supportsFixedPoint_of_no_aggregateWholeSupport
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {label : String}
    (hNoWhole : ¬ AggregateWholeSupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.fixedPoint label) := by
  intro h
  rcases h with ⟨hWhole, _, _, _, _, _, _⟩
  exact hNoWhole hWhole

theorem not_supportsFixedPoint_of_missing_generatedHierarchyReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {label : String}
    (hNoReality : ¬ GeneratedHierarchyRealitySupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.fixedPoint label) := by
  intro h
  rcases h with ⟨_, _, hReality, _, _, _, _⟩
  exact hNoReality hReality

theorem not_supportsFixedPoint_of_missing_closure
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {label : String}
    (hNoClosure : ¬ FixedPointClosureSupport ctx a) :
    ¬ SupportsCountableTier standard ctx (.aggregate a) (.fixedPoint label) := by
  intro h
  rcases h with ⟨_, _, _, _, _, hClosure, _⟩
  exact hNoClosure hClosure

theorem not_supportsFixedPoint_of_missing_generatedHierarchyIndependence
    {ctx : RuleContext} {a : AggregateId} {label : String}
    (hNoIndependence : ¬ FiniteOmegaPowerHierarchyIndependenceSupport ctx a) :
    ¬ SupportsCountableTier .strict ctx (.aggregate a) (.fixedPoint label) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, hIndependence⟩
  exact hNoIndependence hIndependence

theorem supportsOmegaMulNat_requires_totalObject
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaMulNat n)) :
    AggregateWholeSupport ctx a := by
  rcases h with ⟨_, hWhole, _, _, _, _⟩
  exact hWhole

theorem supportsOmegaMulNat_requires_lowerTierReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaMulNat n)) :
    AggregateLowerTierRealitySupport ctx a .omega := by
  rcases h with ⟨_, _, _, hReality, _, _⟩
  exact hReality

theorem supportsOmegaMulNat_requires_lowerTierIndependence
    {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier .strict ctx (.aggregate a) (.omegaMulNat n)) :
    AggregateLowerTierIndependenceSupport ctx a .omega := by
  rcases h with ⟨_, _, _, _, hIndependence, _⟩
  exact hIndependence

theorem supportsOmegaPowNat_two_requires_totalObject
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat 2)) :
    AggregateWholeSupport ctx a := by
  rcases h with ⟨hWhole, _, _, _, _⟩
  exact hWhole

theorem supportsOmegaPowNat_two_requires_lowerTierReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat 2)) :
    AggregateLowerTierRealitySupport ctx a .omega := by
  rcases h with ⟨_, _, hReality, _, _⟩
  exact hReality

theorem supportsOmegaPowNat_two_requires_lowerTierIndependence
    {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier .strict ctx (.aggregate a) (.omegaPowNat 2)) :
    AggregateLowerTierIndependenceSupport ctx a .omega := by
  rcases h with ⟨_, _, _, hIndependence, _⟩
  exact hIndependence

theorem supportsOmegaPowNat_succ_requires_totalObject
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat (n + 3))) :
    AggregateWholeSupport ctx a := by
  rcases h with ⟨hWhole, _, _, _, _⟩
  exact hWhole

theorem supportsOmegaPowNat_succ_requires_lowerTierReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat (n + 3))) :
    AggregateLowerTierRealitySupport ctx a (.omegaPowNat (n + 2)) := by
  rcases h with ⟨_, _, hReality, _, _⟩
  exact hReality

theorem supportsOmegaPowNat_succ_requires_lowerTierIndependence
    {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier .strict ctx (.aggregate a) (.omegaPowNat (n + 3))) :
    AggregateLowerTierIndependenceSupport ctx a (.omegaPowNat (n + 2)) := by
  rcases h with ⟨_, _, _, hIndependence, _⟩
  exact hIndependence

theorem supportsOmegaPowOmega_requires_totalObject
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega) :
    AggregateWholeSupport ctx a := by
  rcases h with ⟨hWhole, _, _, _, _, _⟩
  exact hWhole

theorem supportsOmegaPowOmega_requires_generatedHierarchyReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega) :
    GeneratedHierarchyRealitySupport ctx a := by
  rcases h with ⟨_, _, hReality, _, _, _⟩
  exact hReality

theorem supportsOmegaPowOmega_requires_generatedHierarchyIndependence
    {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier .strict ctx (.aggregate a) .omegaPowOmega) :
    FiniteOmegaPowerHierarchyIndependenceSupport ctx a := by
  rcases h with ⟨_, _, _, _, _, hIndependence⟩
  exact hIndependence

theorem supportsFixedPoint_requires_totalObject
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {label : String}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.fixedPoint label)) :
    AggregateWholeSupport ctx a := by
  rcases h with ⟨hWhole, _, _, _, _, _, _⟩
  exact hWhole

theorem supportsOmegaMulNat_requires_exactMultiplicity
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaMulNat n)) :
    ctx.HasAggregateFact a (.hasExactlyNIndependentMembersAt .omega n) := by
  rcases h with ⟨_, _, _, _, _, hCount⟩
  exact hCount

theorem supportsOmegaPowNat_two_requires_countably_many_omega
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat 2)) :
    ctx.HasAggregateFact a (.hasCountablyManyIndependentMembersAt .omega) := by
  rcases h with ⟨_, _, _, _, hCount⟩
  exact hCount

theorem supportsOmegaPowNat_succ_requires_lowerTier
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {n : Nat}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.omegaPowNat (n + 3))) :
    ctx.HasAggregateFact a (.hasCountablyManyIndependentMembersAt (.omegaPowNat (n + 2))) := by
  rcases h with ⟨_, _, _, _, hCount⟩
  exact hCount

theorem supportsOmegaPowOmega_requires_iteration_rule
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId}
    (h : SupportsCountableTier standard ctx (.aggregate a) .omegaPowOmega) :
    ctx.HasAggregateFact a .describesOmegaPowerSuccessorRule ∧
      ctx.HasAggregateFact a .describesAllFiniteOmegaPowerIterations := by
  rcases h with ⟨_, _, _, hRule, hFinite, _⟩
  exact ⟨hRule, hFinite⟩

theorem supportsFixedPoint_requires_generatedHierarchyReality
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {label : String}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.fixedPoint label)) :
    GeneratedHierarchyRealitySupport ctx a := by
  rcases h with ⟨_, _, hReality, _, _, _, _⟩
  exact hReality

theorem supportsFixedPoint_requires_closure
    {standard : TransfiniteStandard} {ctx : RuleContext} {a : AggregateId} {label : String}
    (h : SupportsCountableTier standard ctx (.aggregate a) (.fixedPoint label)) :
    FixedPointClosureSupport ctx a := by
  rcases h with ⟨_, _, _, _, _, hClosure, _⟩
  exact hClosure

theorem supportsFixedPoint_requires_generatedHierarchyIndependence
    {ctx : RuleContext} {a : AggregateId} {label : String}
    (h : SupportsCountableTier .strict ctx (.aggregate a) (.fixedPoint label)) :
    FiniteOmegaPowerHierarchyIndependenceSupport ctx a := by
  rcases h with ⟨_, _, _, _, _, _, hIndependence⟩
  exact hIndependence

abbrev «聚合整体支持» := AggregateWholeSupport
abbrev «聚合阻断» := AggregateBlocker
abbrev «下层成员实在性支持» := AggregateLowerTierRealitySupport
abbrev «下层成员独立性支持» := AggregateLowerTierIndependenceSupport
abbrev «生成层级实在性支持» := GeneratedHierarchyRealitySupport
abbrev «不动点闭包支持» := FixedPointClosureSupport
abbrev «下层成员彼此独立要求» := LowerTierPeerIndependenceRequired
abbrev «有限ω幂层级独立性支持» := FiniteOmegaPowerHierarchyIndependenceSupport
abbrev «生成层级彼此独立要求» := GeneratedHierarchyPeerIndependenceRequired
abbrev «支持ω乘有限聚合» := SupportsOmegaMulNatAggregate
abbrev «支持ω平方聚合» := SupportsOmegaPowTwoAggregate
abbrev «支持ω后继幂聚合» := SupportsOmegaPowSuccAggregate
abbrev «支持ω的ω次幂聚合» := SupportsOmegaPowOmegaAggregate
abbrev «支持不动点聚合» := SupportsFixedPointAggregate
abbrev «支持可数超限层级» := SupportsCountableTier

end VerseFramework
