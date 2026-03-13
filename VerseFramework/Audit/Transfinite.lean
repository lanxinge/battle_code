import VerseFramework.Core.Claim
import VerseFramework.Audit.Common
import VerseFramework.Rules.Transfinite

namespace VerseFramework

structure CountableTierAudit where
  «标准» : TransfiniteStandard
  «目标» : HierarchyTarget
  «层级» : CountableTier
  «总对象» : ConditionAudit
  «阻断项» : ConditionAudit
  «成员实在性» : ConditionAudit
  «成员独立性» : ConditionAudit
  «生成» : ConditionAudit
  «闭包» : ConditionAudit
  deriving Repr

namespace CountableTierAudit

abbrev standard := CountableTierAudit.«标准»
abbrev target := CountableTierAudit.«目标»
abbrev tier := CountableTierAudit.«层级»
abbrev totalObject := CountableTierAudit.«总对象»
abbrev blocker := CountableTierAudit.«阻断项»
abbrev memberReality := CountableTierAudit.«成员实在性»
abbrev memberIndependence := CountableTierAudit.«成员独立性»
abbrev generation := CountableTierAudit.«生成»
abbrev closure := CountableTierAudit.«闭包»

def proofStatus (audit : CountableTierAudit) : ProofStatus :=
  ProofStatus.merge
    [ audit.totalObject.proofStatus
    , audit.blocker.proofStatus
    , audit.memberReality.proofStatus
    , audit.memberIndependence.proofStatus
    , audit.generation.proofStatus
    , audit.closure.proofStatus ]

def verdict (audit : CountableTierAudit) : Verdict Claim :=
  { «断言» := .countableOrdinalTier audit.standard audit.target audit.tier
    «状态» := audit.proofStatus }

def renderLines (audit : CountableTierAudit) : List String :=
  [ s!"Claim: countable tier ({audit.standard.label}, {reprStr audit.target}, {audit.tier.label})"
  , s!"ProofStatus: {reprStr audit.proofStatus}" ] ++
  audit.totalObject.renderLines ++
  audit.blocker.renderLines ++
  audit.memberReality.renderLines ++
  audit.memberIndependence.renderLines ++
  audit.generation.renderLines ++
  audit.closure.renderLines

end CountableTierAudit

namespace «超限层级审计»

abbrev «标准» := CountableTierAudit.«标准»
abbrev «目标» := CountableTierAudit.«目标»
abbrev «层级» := CountableTierAudit.«层级»
abbrev «总对象» := CountableTierAudit.«总对象»
abbrev «阻断项» := CountableTierAudit.«阻断项»
abbrev «成员实在性» := CountableTierAudit.«成员实在性»
abbrev «成员独立性» := CountableTierAudit.«成员独立性»
abbrev «生成» := CountableTierAudit.«生成»
abbrev «闭包» := CountableTierAudit.«闭包»
abbrev «证明状态» := CountableTierAudit.proofStatus
abbrev «判定» := CountableTierAudit.verdict
abbrev «渲染行» := CountableTierAudit.renderLines

end «超限层级审计»

noncomputable def aggregateWholeAudit
    (ctx : RuleContext) (a : AggregateId) : ConditionAudit := by
  classical
  if h : AggregateWholeSupport ctx a then
    exact
      { «标签» := "AggregateWholeObject"
        «来源» := .directText
        «注记» := ctx.AggregateAuditTrail a .presentedAsTotalObject }
  else
    exact
      { «标签» := "AggregateWholeObject"
        «来源» := .missing
        «注记» := [ "Missing an explicit statement that the transfinite aggregate is recognized as one total object." ] }

noncomputable def aggregateBlockerAudit
    (ctx : RuleContext) (a : AggregateId) : ConditionAudit := by
  classical
  if h : AggregateBlocker ctx a then
    exact
      { «标签» := "AggregateFrameworkBlocker"
        «来源» := .blocked
        «注记» := ctx.AggregateAuditTrail a .presentedAsFrameworkOnly }
  else
    exact
      { «标签» := "AggregateFrameworkBlocker"
        «来源» := .structuralWitness
        «注记» := [ "No framework-only blocker is attached to this aggregate target." ] }

noncomputable def lowerTierRealityAudit
    (ctx : RuleContext) (a : AggregateId) (tier : CountableTier) : ConditionAudit := by
  classical
  if h : AggregateLowerTierRealitySupport ctx a tier then
    exact
      { «标签» := s!"LowerTierReality({tier.label})"
        «来源» := .directText
        «注记» := ctx.AggregateAuditTrail a (.membersRealizeTierObjectsAt tier) }
  else
    exact
      { «标签» := s!"LowerTierReality({tier.label})"
        «来源» := .missing
        «注记» :=
          [ s!"Need explicit text that the {tier.label}-level members are realized lower-tier objects, not bare labels, placeholders, or a merely schematic hierarchy." ] }

noncomputable def lowerTierIndependenceAudit
    (ctx : RuleContext) (a : AggregateId) (tier : CountableTier) : ConditionAudit := by
  classical
  let causalNotes :=
    if h : ctx.HasAggregateFact a (.membersArePairwiseCausallyIndependentAt tier) then
      ctx.AggregateAuditTrail a (.membersArePairwiseCausallyIndependentAt tier)
    else
      [ s!"Missing explicit causal isolation among the {tier.label}-level members." ]
  let dynamicNotes :=
    if h : ctx.HasAggregateFact a (.membersArePairwiseDynamicallyIndependentAt tier) then
      ctx.AggregateAuditTrail a (.membersArePairwiseDynamicallyIndependentAt tier)
    else
      [ s!"Missing explicit dynamic independence among the {tier.label}-level members." ]
  let externalNotes :=
    if h : ctx.HasAggregateFact a (.membersDoNotRequireExternalSupportAt tier) then
      ctx.AggregateAuditTrail a (.membersDoNotRequireExternalSupportAt tier)
    else
      [ s!"Missing explicit support that each {tier.label}-level member remains complete without external sustaining structure or governance." ]
  if h : AggregateLowerTierIndependenceSupport ctx a tier then
    exact
      { «标签» := s!"LowerTierIndependence({tier.label})"
        «来源» := .directText
        «注记» := causalNotes ++ dynamicNotes ++ externalNotes }
  else
    exact
      { «标签» := s!"LowerTierIndependence({tier.label})"
        «来源» := .missing
        «注记» := causalNotes ++ dynamicNotes ++ externalNotes }

noncomputable def generatedHierarchyRealityAudit
    (ctx : RuleContext) (a : AggregateId) : ConditionAudit := by
  classical
  if h : GeneratedHierarchyRealitySupport ctx a then
    exact
      { «标签» := "GeneratedHierarchyReality"
        «来源» := .directText
        «注记» := ctx.AggregateAuditTrail a .generatedHierarchyPresentedAsActualObjects }
  else
    exact
      { «标签» := "GeneratedHierarchyReality"
        «来源» := .missing
        «注记» :=
          [ "Need explicit text that the recursively generated hierarchy is treated as an actually realized collection of layers, not merely a rule for producing possible layers." ] }

noncomputable def generatedHierarchyIndependenceAudit
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (a : AggregateId) : ConditionAudit := by
  classical
  match standard with
  | .lenient =>
      exact
        { «标签» := "GeneratedHierarchyIndependence"
          «来源» := .structuralWitness
          «注记» :=
            [ "Lenient transfinite standard does not require peer independence across every generated finite omega-power predecessor layer." ] }
  | .strict =>
      let omegaNotes :=
        if h : AggregateLowerTierIndependenceSupport ctx a .omega then
          (lowerTierIndependenceAudit ctx a .omega).notes
        else
          [ "Missing the base omega-level peer-independence support required by the strict transfinite standard." ]
      if h : FiniteOmegaPowerHierarchyIndependenceSupport ctx a then
        exact
          { «标签» := "GeneratedHierarchyIndependence"
            «来源» := .directText
            «注记» :=
              [ "Strict transfinite standard requires peer independence at omega and every finite generated omega-power predecessor layer." ]
              ++ omegaNotes ++
              [ "All finite omega-power predecessor layers are covered by aggregate-level pairwise independence and external self-sufficiency evidence." ] }
      else
        exact
          { «标签» := "GeneratedHierarchyIndependence"
            «来源» := .missing
            «注记» :=
              [ "Strict transfinite standard requires peer independence at omega and every finite generated omega-power predecessor layer." ]
              ++ omegaNotes ++
              [ "Missing aggregate-level evidence that every finite omega-power predecessor layer has pairwise causal independence, dynamic independence, and external self-sufficiency." ] }

noncomputable def countableTierMemberRealityAudit
    (ctx : RuleContext) (target : HierarchyTarget) (tier : CountableTier) : ConditionAudit := by
  classical
  match tier with
  | .omega =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberReality"
              «来源» := .structuralWitness
              «注记» := [ "Tier omega targets one strict monadic world, so object-level reality is discharged by the monadic judgement itself." ] }
      | .aggregate _ =>
          exact
            { «标签» := "MemberReality"
              «来源» := .missing
              «注记» := [ "Tier omega must target one monadic world, not an aggregate object." ] }
  | .omegaMulNat n =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberReality"
              «来源» := .structuralWitness
              «注记» := [ "Member-reality checks for omega*n apply only to aggregate targets." ] }
      | .aggregate a =>
          if hInvalid : ¬ 2 ≤ n then
            exact
              { «标签» := "MemberReality"
                «来源» := .missing
                «注记» := [ "omega*n is only used here for n >= 2; tier omega itself should use the monadic rule." ] }
          else
            exact lowerTierRealityAudit ctx a .omega
  | .omegaPowNat n =>
      match n with
      | 0 =>
          exact
            { «标签» := "MemberReality"
              «来源» := .structuralWitness
              «注记» := [ "No lower-tier member-reality check applies because omega^0 is outside this checker." ] }
      | 1 =>
          exact
            { «标签» := "MemberReality"
              «来源» := .structuralWitness
              «注记» := [ "No lower-tier member-reality check applies because omega^1 is handled as tier omega." ] }
      | 2 =>
          match target with
          | .world _ =>
              exact
                { «标签» := "MemberReality"
                  «来源» := .structuralWitness
                  «注记» := [ "Member-reality checks for omega^2 apply only to aggregate targets." ] }
          | .aggregate a =>
              exact lowerTierRealityAudit ctx a .omega
      | m + 3 =>
          match target with
          | .world _ =>
              exact
                { «标签» := "MemberReality"
                  «来源» := .structuralWitness
                  «注记» := [ "Higher omega-power tiers require an aggregate target before lower-tier members can be audited." ] }
          | .aggregate a =>
              exact lowerTierRealityAudit ctx a (.omegaPowNat (m + 2))
  | .omegaPowOmega =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberReality"
              «来源» := .structuralWitness
              «注记» := [ "omega^omega must target an aggregate object before recursive hierarchy reality can be audited." ] }
      | .aggregate a =>
          exact generatedHierarchyRealityAudit ctx a
  | .fixedPoint _ =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberReality"
              «来源» := .structuralWitness
              «注记» := [ "A fixed-point tier must target an aggregate object before recursive hierarchy reality can be audited." ] }
      | .aggregate a =>
          exact generatedHierarchyRealityAudit ctx a

noncomputable def countableTierMemberIndependenceAudit
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (target : HierarchyTarget) (tier : CountableTier) : ConditionAudit := by
  classical
  match tier with
  | .omega =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberIndependence"
              «来源» := .structuralWitness
              «注记» := [ "Tier omega inherits internal independence from the strict monadic-world judgement." ] }
      | .aggregate _ =>
          exact
            { «标签» := "MemberIndependence"
              «来源» := .missing
              «注记» := [ "Tier omega does not support an aggregate-level member independence audit." ] }
  | .omegaMulNat n =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberIndependence"
              «来源» := .structuralWitness
              «注记» := [ "Member-independence checks for omega*n apply only to aggregate targets." ] }
      | .aggregate a =>
          if hInvalid : ¬ 2 ≤ n then
            exact
              { «标签» := "MemberIndependence"
                «来源» := .missing
                «注记» := [ "omega*n is only used here for n >= 2; tier omega itself should use the monadic rule." ] }
          else
            match standard with
            | .strict => exact lowerTierIndependenceAudit ctx a .omega
            | .lenient =>
                exact
                  { «标签» := "MemberIndependence"
                    «来源» := .structuralWitness
                    «注记» := [ "Lenient transfinite standard does not require peer independence among the omega-level members used by this aggregate claim." ] }
  | .omegaPowNat n =>
      match n with
      | 0 =>
          exact
            { «标签» := "MemberIndependence"
              «来源» := .structuralWitness
              «注记» := [ "No lower-tier member-independence check applies because omega^0 is outside this checker." ] }
      | 1 =>
          exact
            { «标签» := "MemberIndependence"
              «来源» := .structuralWitness
              «注记» := [ "No lower-tier member-independence check applies because omega^1 is handled as tier omega." ] }
      | 2 =>
          match target with
          | .world _ =>
              exact
                { «标签» := "MemberIndependence"
                  «来源» := .structuralWitness
                  «注记» := [ "Member-independence checks for omega^2 apply only to aggregate targets." ] }
          | .aggregate a =>
              match standard with
              | .strict => exact lowerTierIndependenceAudit ctx a .omega
              | .lenient =>
                  exact
                    { «标签» := "MemberIndependence"
                      «来源» := .structuralWitness
                      «注记» := [ "Lenient transfinite standard does not require peer independence among the omega-level members used to justify omega^2." ] }
      | m + 3 =>
          match target with
          | .world _ =>
              exact
                { «标签» := "MemberIndependence"
                  «来源» := .structuralWitness
                  «注记» := [ "Higher omega-power tiers require an aggregate target before lower-tier independence can be audited." ] }
          | .aggregate a =>
              match standard with
              | .strict => exact lowerTierIndependenceAudit ctx a (.omegaPowNat (m + 2))
              | .lenient =>
                  exact
                    { «标签» := "MemberIndependence"
                      «来源» := .structuralWitness
                      «注记» := [ "Lenient transfinite standard does not require peer independence among the immediate lower-tier members used by this higher omega-power claim." ] }
  | .omegaPowOmega =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberIndependence"
              «来源» := .structuralWitness
              «注记» := [ "omega^omega audits independence through the realized lower-tier hierarchy, not through a single world target." ] }
      | .aggregate a =>
          exact generatedHierarchyIndependenceAudit standard ctx a
  | .fixedPoint _ =>
      match target with
      | .world _ =>
          exact
            { «标签» := "MemberIndependence"
              «来源» := .structuralWitness
              «注记» := [ "Fixed-point tiers audit independence through the recursively generated lower tiers, not through a single world target." ] }
      | .aggregate a =>
          exact generatedHierarchyIndependenceAudit standard ctx a

noncomputable def countableTierGenerationAudit
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (target : HierarchyTarget) (tier : CountableTier) : ConditionAudit := by
  classical
  match tier, target with
  | .omega, .world u =>
      if h : SupportsCountableTier standard ctx (.world u) .omega then
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .structuralWitness
            «注记» := [ "Base tier omega reuses the strict monadic-universe judgement on a world target." ] }
      else
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .missing
            «注记» := [ "Need one complete monadic-universe object to justify tier omega." ] }
  | .omega, .aggregate _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "Tier omega must target a single monadic universe object, not an aggregate." ] }
  | .omegaMulNat _, .world _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "A finite omega*n aggregate must target an aggregate object, not one world." ] }
  | .omegaMulNat n, .aggregate a =>
      if hInvalid : ¬ 2 ≤ n then
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .missing
            «注记» := [ "omega*n is only used here for n >= 2; tier omega itself should use the monadic rule." ] }
      else if h : ctx.HasAggregateFact a (.hasExactlyNIndependentMembersAt .omega n) then
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .directText
            «注记» := ctx.AggregateAuditTrail a (.hasExactlyNIndependentMembersAt .omega n) }
      else
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .missing
            «注记» := [ "Need explicit text evidence that the aggregate has exactly n omega-level members. Their object-reality and peer-independence are audited separately." ] }
  | .omegaPowNat 0, _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "omega^0 is outside this checker; transfinite aggregation starts here from omega or above." ] }
  | .omegaPowNat 1, _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "omega^1 should be handled as tier omega, not as an aggregate power target." ] }
  | .omegaPowNat 2, .world _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "omega^2 must target an aggregate object, not one world." ] }
  | .omegaPowNat 2, .aggregate a =>
      if h : ctx.HasAggregateFact a (.hasCountablyManyIndependentMembersAt .omega) then
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .directText
            «注记» := ctx.AggregateAuditTrail a (.hasCountablyManyIndependentMembersAt .omega) }
      else
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .missing
            «注记» := [ "Need explicit text evidence that the aggregate contains countably many omega-level members. Their object-reality and peer-independence are audited separately." ] }
  | .omegaPowNat (n + 3), .world _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "omega^(n+1) aggregates above omega must target an aggregate object." ] }
  | .omegaPowNat (n + 3), .aggregate a =>
      if h : ctx.HasAggregateFact a (.hasCountablyManyIndependentMembersAt (.omegaPowNat (n + 2))) then
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .directText
            «注记» := ctx.AggregateAuditTrail a (.hasCountablyManyIndependentMembersAt (.omegaPowNat (n + 2))) }
      else
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .missing
            «注记» := [ "Need explicit text evidence that the aggregate contains countably many lower-tier members. Their object-reality and peer-independence are audited separately." ] }
  | .omegaPowOmega, .world _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "omega^omega must target an aggregate object." ] }
  | .omegaPowOmega, .aggregate a =>
      if h1 : ctx.HasAggregateFact a .describesOmegaPowerSuccessorRule then
        if h2 : ctx.HasAggregateFact a .describesAllFiniteOmegaPowerIterations then
          exact
            { «标签» := "CountableTierGeneration"
              «来源» := .directText
              «注记» :=
                ctx.AggregateAuditTrail a .describesOmegaPowerSuccessorRule ++
                ctx.AggregateAuditTrail a .describesAllFiniteOmegaPowerIterations }
        else
          exact
            { «标签» := "CountableTierGeneration"
              «来源» := .missing
              «注记» := [ "Need explicit permission to continue the omega-power construction through all finite iterations." ] }
      else
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .missing
            «注记» := [ "Need an explicit recursive generation rule of the form alpha ↦ omega^alpha or an equivalent finite power-tower rule." ] }
  | .fixedPoint label, .world _ =>
      exact
        { «标签» := "CountableTierGeneration"
          «来源» := .missing
          «注记» := [ "A fixed-point ordinal tier must target an aggregate object." ] }
  | .fixedPoint label, .aggregate a =>
      if h1 : ctx.HasAggregateFact a .describesOmegaPowerSuccessorRule then
        if h2 : ctx.HasAggregateFact a .describesAllFiniteOmegaPowerIterations then
          exact
            { «标签» := "CountableTierGeneration"
              «来源» := .directText
              «注记» :=
                [ s!"Fixed-point tier target: {label}" ] ++
                ctx.AggregateAuditTrail a .describesOmegaPowerSuccessorRule ++
                ctx.AggregateAuditTrail a .describesAllFiniteOmegaPowerIterations }
        else
          exact
            { «标签» := "CountableTierGeneration"
              «来源» := .missing
              «注记» := [ "Need explicit permission to continue all finite omega-power iterations before a fixed-point closure can be claimed." ] }
      else
        exact
          { «标签» := "CountableTierGeneration"
            «来源» := .missing
            «注记» := [ "Need an explicit omega-power recursive generation rule before a fixed-point tier can be claimed." ] }

noncomputable def countableTierClosureAudit
    (ctx : RuleContext) (target : HierarchyTarget) (tier : CountableTier) : ConditionAudit := by
  classical
  match tier, target with
  | .fixedPoint label, .aggregate a =>
      if hClosure : FixedPointClosureSupport ctx a then
        let limitNotes :=
          if h : ctx.HasAggregateFact a .describesLimitClosureOfPreviousLayers then
            ctx.AggregateAuditTrail a .describesLimitClosureOfPreviousLayers
          else []
        let diagonalNotes :=
          if h : ctx.HasAggregateFact a .describesDiagonalClosure then
            ctx.AggregateAuditTrail a .describesDiagonalClosure
          else []
        let recursiveNotes :=
          if h : ctx.HasAggregateFact a .describesOrdinalRecursiveGenerator then
            ctx.AggregateAuditTrail a .describesOrdinalRecursiveGenerator
          else []
        exact
          { «标签» := "FixedPointClosure"
            «来源» := .directText
            «注记» := [ s!"Fixed-point closure target: {label}" ] ++
              limitNotes ++ diagonalNotes ++ recursiveNotes }
      else
        exact
          { «标签» := "FixedPointClosure"
            «来源» := .missing
            «注记» := [ "Need a diagonal, limit, or ordinal-recursive closure description that turns the recursively generated hierarchy into one fixed-point object." ] }
  | .fixedPoint _, .world _ =>
      exact
        { «标签» := "FixedPointClosure"
          «来源» := .missing
          «注记» := [ "A fixed-point closure claim cannot target a single world object." ] }
  | _, _ =>
      exact
        { «标签» := "FixedPointClosure"
          «来源» := .structuralWitness
          «注记» := [ "No extra fixed-point closure requirement applies at this tier." ] }

noncomputable def countableTierAudit
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (target : HierarchyTarget) (tier : CountableTier) : CountableTierAudit :=
  let totalObject :=
    match target with
    | .world _ =>
        { «标签» := "AggregateWholeObject"
          «来源» := .structuralWitness
          «注记» := [ "World-target tiers do not require a separate aggregate-whole annotation." ] }
    | .aggregate a => aggregateWholeAudit ctx a
  let blocker :=
    match target with
    | .world _ =>
        { «标签» := "AggregateFrameworkBlocker"
          «来源» := .structuralWitness
          «注记» := [ "No aggregate framework blocker applies to a world target." ] }
    | .aggregate a => aggregateBlockerAudit ctx a
  { «标准» := standard
    «目标» := target
    «层级» := tier
    «总对象» := totalObject
    «阻断项» := blocker
    «成员实在性» := countableTierMemberRealityAudit ctx target tier
    «成员独立性» := countableTierMemberIndependenceAudit standard ctx target tier
    «生成» := countableTierGenerationAudit standard ctx target tier
    «闭包» := countableTierClosureAudit ctx target tier }

noncomputable def countableTierVerdict
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (target : HierarchyTarget) (tier : CountableTier) : Verdict Claim :=
  (countableTierAudit standard ctx target tier).verdict

abbrev «超限层级审计» := CountableTierAudit
noncomputable abbrev «聚合整体审计» := aggregateWholeAudit
noncomputable abbrev «聚合阻断项审计» := aggregateBlockerAudit
noncomputable abbrev «下层成员实在性审计» := lowerTierRealityAudit
noncomputable abbrev «下层成员独立性审计» := lowerTierIndependenceAudit
noncomputable abbrev «生成层级实在性审计» := generatedHierarchyRealityAudit
noncomputable abbrev «生成层级独立性审计» := generatedHierarchyIndependenceAudit
noncomputable abbrev «可数超限成员实在性审计» := countableTierMemberRealityAudit
noncomputable abbrev «可数超限成员独立性审计» := countableTierMemberIndependenceAudit
noncomputable abbrev «可数超限生成审计» := countableTierGenerationAudit
noncomputable abbrev «可数超限闭包审计» := countableTierClosureAudit
noncomputable abbrev «超限层级判定» := countableTierVerdict

end VerseFramework
