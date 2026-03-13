import VerseFramework.Rules.Policy
import VerseFramework.Rules.Witness.Common

namespace VerseFramework

inductive SpatialSupportWitness (ctx : RuleContext) (u : WorldId) : Prop where
  | spatialAspect (h : WorldFactWitness ctx u .hasSpatialAspect)
  | connectedSpacetime (h : WorldFactWitness ctx u .connectedSpacetimeObject)

def SpatialSupportWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : SpatialSupportWitness ctx u) :
    SpatialSupport ctx u := by
  cases w with
  | spatialAspect h => exact Or.inl h.proves
  | connectedSpacetime h => exact Or.inr h.proves

theorem spatialSupport_iff_witness (ctx : RuleContext) (u : WorldId) :
    SpatialSupport ctx u ↔ SpatialSupportWitness ctx u := by
  constructor
  · intro h
    rcases h with h | h
    · exact .spatialAspect (.direct h)
    · exact .connectedSpacetime (.direct h)
  · intro h
    exact h.proves

abbrev «空间支持见证» := SpatialSupportWitness
abbrev «空间支持当且仅当存在见证» := spatialSupport_iff_witness

inductive TemporalSupportWitness (ctx : RuleContext) (u : WorldId) : Prop where
  | temporalAspect (h : WorldFactWitness ctx u .hasTemporalAspect)
  | connectedSpacetime (h : WorldFactWitness ctx u .connectedSpacetimeObject)
  | historyBridge
      (hAssumption : AssumptionWitness ctx .temporalFromWorldHistory)
      (hHistory : WorldFactWitness ctx u .hasWorldHistory)
  | realistBridge
      (hAssumption : AssumptionWitness ctx .weakRealistCosmology)
      (hSetting : WorldFactWitness ctx u .presentedInRealistPhysicsSetting)
      (hSpatial : WorldFactWitness ctx u .hasSpatialAspect)

def TemporalSupportWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : TemporalSupportWitness ctx u) :
    TemporalSupport ctx u := by
  cases w with
  | temporalAspect h => exact Or.inl h.proves
  | connectedSpacetime h => exact Or.inr (Or.inl h.proves)
  | historyBridge hAssumption hHistory =>
      exact Or.inr (Or.inr (Or.inl ⟨hAssumption.proves, hHistory.proves⟩))
  | realistBridge hAssumption hSetting hSpatial =>
      exact Or.inr (Or.inr (Or.inr ⟨hAssumption.proves, hSetting.proves, hSpatial.proves⟩))

theorem temporalSupport_iff_witness (ctx : RuleContext) (u : WorldId) :
    TemporalSupport ctx u ↔ TemporalSupportWitness ctx u := by
  constructor
  · intro h
    rcases h with h | h
    · exact .temporalAspect (.direct h)
    · rcases h with h | h
      · exact .connectedSpacetime (.direct h)
      · rcases h with h | h
        · exact .historyBridge (.enabled h.1) (.direct h.2)
        · exact .realistBridge (.enabled h.1) (.direct h.2.1) (.direct h.2.2)
  · intro h
    exact h.proves

abbrev «时间支持见证» := TemporalSupportWitness
abbrev «时间支持当且仅当存在见证» := temporalSupport_iff_witness

inductive AutonomousEvolutionSupportWitness (ctx : RuleContext) (u : WorldId) : Prop where
  | directAutonomousEvolution (h : WorldFactWitness ctx u .hasAutonomousEvolution)
  | fromUnifiedDynamics (h : WorldFactWitness ctx u .hasUnifiedDynamics)
  | historyBridge
      (hAssumption : AssumptionWitness ctx .autonomousEvolutionFromHistory)
      (hHistory : WorldFactWitness ctx u .hasWorldHistory)
      (hGlobal : WorldFactWitness ctx u .hasGlobalEvolution)
  | realistBridge
      (hAssumption : AssumptionWitness ctx .weakRealistCosmology)
      (hSetting : WorldFactWitness ctx u .presentedInRealistPhysicsSetting)
      (hHistory : WorldFactWitness ctx u .hasWorldHistory)

def AutonomousEvolutionSupportWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : AutonomousEvolutionSupportWitness ctx u) :
    AutonomousEvolutionSupport ctx u := by
  cases w with
  | directAutonomousEvolution h => exact Or.inl h.proves
  | fromUnifiedDynamics h => exact Or.inr (Or.inl h.proves)
  | historyBridge hAssumption hHistory hGlobal =>
      exact Or.inr (Or.inr (Or.inl ⟨hAssumption.proves, hHistory.proves, hGlobal.proves⟩))
  | realistBridge hAssumption hSetting hHistory =>
      exact Or.inr (Or.inr (Or.inr ⟨hAssumption.proves, hSetting.proves, hHistory.proves⟩))

theorem autonomousEvolutionSupport_iff_witness (ctx : RuleContext) (u : WorldId) :
    AutonomousEvolutionSupport ctx u ↔ AutonomousEvolutionSupportWitness ctx u := by
  constructor
  · intro h
    rcases h with h | h
    · exact .directAutonomousEvolution (.direct h)
    · rcases h with h | h
      · exact .fromUnifiedDynamics (.direct h)
      · rcases h with h | h
        · exact .historyBridge (.enabled h.1) (.direct h.2.1) (.direct h.2.2)
        · exact .realistBridge (.enabled h.1) (.direct h.2.1) (.direct h.2.2)
  · intro h
    exact h.proves

abbrev «自治演化支持见证» := AutonomousEvolutionSupportWitness
abbrev «自治演化支持当且仅当存在见证» := autonomousEvolutionSupport_iff_witness

def UnifiedDynamicsLawSupport (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .hasUnifiedDynamics ∨
  (ctx.assumptions.allows .unifiedDynamicsFromHistory ∧
    ctx.HasWorldFact u .hasWorldHistory ∧
    ctx.HasWorldFact u .hasGlobalEvolution) ∨
  (ctx.assumptions.allows .weakRealistCosmology ∧
    ctx.HasWorldFact u .presentedInRealistPhysicsSetting ∧
    ctx.HasWorldFact u .hasWorldHistory)

inductive UnifiedDynamicsLawWitness (ctx : RuleContext) (u : WorldId) : Prop where
  | directUnifiedDynamics (h : WorldFactWitness ctx u .hasUnifiedDynamics)
  | historyBridge
      (hAssumption : AssumptionWitness ctx .unifiedDynamicsFromHistory)
      (hHistory : WorldFactWitness ctx u .hasWorldHistory)
      (hGlobal : WorldFactWitness ctx u .hasGlobalEvolution)
  | realistBridge
      (hAssumption : AssumptionWitness ctx .weakRealistCosmology)
      (hSetting : WorldFactWitness ctx u .presentedInRealistPhysicsSetting)
      (hHistory : WorldFactWitness ctx u .hasWorldHistory)

def UnifiedDynamicsLawWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : UnifiedDynamicsLawWitness ctx u) :
    UnifiedDynamicsLawSupport ctx u := by
  cases w with
  | directUnifiedDynamics h => exact Or.inl h.proves
  | historyBridge hAssumption hHistory hGlobal =>
      exact Or.inr (Or.inl ⟨hAssumption.proves, hHistory.proves, hGlobal.proves⟩)
  | realistBridge hAssumption hSetting hHistory =>
      exact Or.inr (Or.inr ⟨hAssumption.proves, hSetting.proves, hHistory.proves⟩)

theorem unifiedDynamicsLawSupport_iff_witness (ctx : RuleContext) (u : WorldId) :
    UnifiedDynamicsLawSupport ctx u ↔ UnifiedDynamicsLawWitness ctx u := by
  constructor
  · intro h
    rcases h with h | h
    · exact .directUnifiedDynamics (.direct h)
    · rcases h with h | h
      · exact .historyBridge (.enabled h.1) (.direct h.2.1) (.direct h.2.2)
      · exact .realistBridge (.enabled h.1) (.direct h.2.1) (.direct h.2.2)
  · intro h
    exact h.proves

abbrev «统一动力学定律支持见证» := UnifiedDynamicsLawWitness
abbrev «统一动力学定律支持当且仅当存在见证» := unifiedDynamicsLawSupport_iff_witness

structure DynamicsSupportWitness (ctx : RuleContext) (u : WorldId) : Prop where
  «定律» : UnifiedDynamicsLawWitness ctx u
  «自主演化» : AutonomousEvolutionSupportWitness ctx u

namespace DynamicsSupportWitness

abbrev law {ctx : RuleContext} {u : WorldId} := @DynamicsSupportWitness.«定律» ctx u
abbrev autonomy {ctx : RuleContext} {u : WorldId} := @DynamicsSupportWitness.«自主演化» ctx u

end DynamicsSupportWitness

def DynamicsSupportWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : DynamicsSupportWitness ctx u) :
    DynamicsSupport ctx u :=
  ⟨w.law.proves, w.autonomy.proves⟩

theorem dynamicsSupport_iff_witness (ctx : RuleContext) (u : WorldId) :
    DynamicsSupport ctx u ↔ DynamicsSupportWitness ctx u := by
  constructor
  · intro h
    refine { «定律» := ?_, «自主演化» := ?_ }
    · exact (unifiedDynamicsLawSupport_iff_witness ctx u).mp h.1
    · exact (autonomousEvolutionSupport_iff_witness ctx u).mp h.2
  · intro h
    exact h.proves

abbrev «动力学支持见证» := DynamicsSupportWitness
abbrev «动力学支持当且仅当存在见证» := dynamicsSupport_iff_witness

inductive WholeWorldSupportWitness (ctx : RuleContext) (u : WorldId) : Prop where
  | directWholeWorld (h : WorldFactWitness ctx u .presentedAsWholeWorld)
  | explicitUniverseBridge
      (hAssumption : AssumptionWitness ctx .wholeWorldFromExplicitUniverseLabel)
      (hUniverseLabel : WorldFactWitness ctx u .explicitlyCalledUniverse)

def WholeWorldSupportWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : WholeWorldSupportWitness ctx u) :
    WholeWorldSupport ctx u := by
  cases w with
  | directWholeWorld h => exact Or.inl h.proves
  | explicitUniverseBridge hAssumption hUniverseLabel =>
      exact Or.inr ⟨hAssumption.proves, hUniverseLabel.proves⟩

theorem wholeWorldSupport_iff_witness (ctx : RuleContext) (u : WorldId) :
    WholeWorldSupport ctx u ↔ WholeWorldSupportWitness ctx u := by
  constructor
  · intro h
    rcases h with h | h
    · exact .directWholeWorld (.direct h)
    · exact .explicitUniverseBridge (.enabled h.1) (.direct h.2)
  · intro h
    exact h.proves

abbrev «完整世界支持见证» := WholeWorldSupportWitness
abbrev «完整世界支持当且仅当存在见证» := wholeWorldSupport_iff_witness

inductive ConnectedWitness (ctx : RuleContext) (u : WorldId) : Prop where
  | directConnected (h : WorldFactWitness ctx u .connectedSpacetimeObject)
  | cauchyBridge
      (hAssumption : AssumptionWitness ctx .connectedFromCauchyLikeSlices)
      (hSlice : WorldFactWitness ctx u .hasCauchyLikeSlices)
      (hSpatial : SpatialSupportWitness ctx u)
      (hTemporal : TemporalSupportWitness ctx u)

def ConnectedWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : ConnectedWitness ctx u) :
    Connected ctx u := by
  cases w with
  | directConnected h => exact Or.inl h.proves
  | cauchyBridge hAssumption hSlice hSpatial hTemporal =>
      exact Or.inr ⟨hAssumption.proves, hSlice.proves, hSpatial.proves, hTemporal.proves⟩

theorem connected_iff_witness (ctx : RuleContext) (u : WorldId) :
    Connected ctx u ↔ ConnectedWitness ctx u := by
  constructor
  · intro h
    rcases h with h | h
    · exact .directConnected (.direct h)
    · refine .cauchyBridge (.enabled h.1) (.direct h.2.1) ?_ ?_
      · exact (spatialSupport_iff_witness ctx u).mp h.2.2.1
      · exact (temporalSupport_iff_witness ctx u).mp h.2.2.2
  · intro h
    exact h.proves

abbrev «连通见证» := ConnectedWitness
abbrev «连通当且仅当存在见证» := connected_iff_witness

structure SpatiotemporalWitness (ctx : RuleContext) (u : WorldId) : Prop where
  «空间» : SpatialSupportWitness ctx u
  «时间» : TemporalSupportWitness ctx u

namespace SpatiotemporalWitness

abbrev spatial {ctx : RuleContext} {u : WorldId} := @SpatiotemporalWitness.«空间» ctx u
abbrev temporal {ctx : RuleContext} {u : WorldId} := @SpatiotemporalWitness.«时间» ctx u

end SpatiotemporalWitness

def SpatiotemporalWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : SpatiotemporalWitness ctx u) :
    Spatiotemporal ctx u :=
  ⟨w.spatial.proves, w.temporal.proves⟩

theorem spatiotemporal_iff_witness (ctx : RuleContext) (u : WorldId) :
    Spatiotemporal ctx u ↔ SpatiotemporalWitness ctx u := by
  constructor
  · intro h
    exact { «空间» := (spatialSupport_iff_witness ctx u).mp h.1
          , «时间» := (temporalSupport_iff_witness ctx u).mp h.2 }
  · intro h
    exact h.proves

abbrev «时空性见证» := SpatiotemporalWitness
abbrev «时空性当且仅当存在见证» := spatiotemporal_iff_witness

structure AutonomousWorldDynamicsWitness (ctx : RuleContext) (u : WorldId) : Prop where
  «支持» : AutonomousEvolutionSupportWitness ctx u
  «无阻断» : ¬ DynamicsDependenceBlocker ctx u

namespace AutonomousWorldDynamicsWitness

abbrev support {ctx : RuleContext} {u : WorldId} := @AutonomousWorldDynamicsWitness.«支持» ctx u
abbrev noBlock {ctx : RuleContext} {u : WorldId} := @AutonomousWorldDynamicsWitness.«无阻断» ctx u

end AutonomousWorldDynamicsWitness

def AutonomousWorldDynamicsWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : AutonomousWorldDynamicsWitness ctx u) :
    AutonomousWorldDynamics ctx u :=
  ⟨w.support.proves, w.noBlock⟩

theorem autonomousWorldDynamics_iff_witness (ctx : RuleContext) (u : WorldId) :
    AutonomousWorldDynamics ctx u ↔ AutonomousWorldDynamicsWitness ctx u := by
  constructor
  · intro h
    exact { «支持» := (autonomousEvolutionSupport_iff_witness ctx u).mp h.1
          , «无阻断» := h.2 }
  · intro h
    exact h.proves

abbrev «自治世界动力学见证» := AutonomousWorldDynamicsWitness
abbrev «自治世界动力学当且仅当存在见证» := autonomousWorldDynamics_iff_witness

structure DynamicallyUnifiedWitness (ctx : RuleContext) (u : WorldId) : Prop where
  «支持» : DynamicsSupportWitness ctx u
  «无阻断» : ¬ DynamicsDependenceBlocker ctx u

namespace DynamicallyUnifiedWitness

abbrev support {ctx : RuleContext} {u : WorldId} := @DynamicallyUnifiedWitness.«支持» ctx u
abbrev noBlock {ctx : RuleContext} {u : WorldId} := @DynamicallyUnifiedWitness.«无阻断» ctx u

end DynamicallyUnifiedWitness

def DynamicallyUnifiedWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : DynamicallyUnifiedWitness ctx u) :
    DynamicallyUnified ctx u :=
  ⟨w.support.proves, w.noBlock⟩

theorem dynamicallyUnified_iff_witness (ctx : RuleContext) (u : WorldId) :
    DynamicallyUnified ctx u ↔ DynamicallyUnifiedWitness ctx u := by
  constructor
  · intro h
    exact { «支持» := (dynamicsSupport_iff_witness ctx u).mp h.1
          , «无阻断» := h.2 }
  · intro h
    exact h.proves

abbrev «动力统一见证» := DynamicallyUnifiedWitness
abbrev «动力统一当且仅当存在见证» := dynamicallyUnified_iff_witness

structure WorldCoreStructureWitness (ctx : RuleContext) (u : WorldId) : Prop where
  «连通» : ConnectedWitness ctx u
  «时空» : SpatiotemporalWitness ctx u
  «动力学» : DynamicallyUnifiedWitness ctx u

namespace WorldCoreStructureWitness

abbrev connected {ctx : RuleContext} {u : WorldId} := @WorldCoreStructureWitness.«连通» ctx u
abbrev spatiotemporal {ctx : RuleContext} {u : WorldId} := @WorldCoreStructureWitness.«时空» ctx u
abbrev dynamics {ctx : RuleContext} {u : WorldId} := @WorldCoreStructureWitness.«动力学» ctx u

end WorldCoreStructureWitness

def WorldCoreStructureWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : WorldCoreStructureWitness ctx u) :
    WorldCoreStructure ctx u :=
  ⟨w.connected.proves, w.spatiotemporal.proves, w.dynamics.proves⟩

theorem worldCoreStructure_iff_witness (ctx : RuleContext) (u : WorldId) :
    WorldCoreStructure ctx u ↔ WorldCoreStructureWitness ctx u := by
  constructor
  · intro h
    exact { «连通» := (connected_iff_witness ctx u).mp h.1
          , «时空» := (spatiotemporal_iff_witness ctx u).mp h.2.1
          , «动力学» := (dynamicallyUnified_iff_witness ctx u).mp h.2.2 }
  · intro h
    exact h.proves

abbrev «世界核心结构见证» := WorldCoreStructureWitness
abbrev «世界核心结构当且仅当存在见证» := worldCoreStructure_iff_witness

structure IndependentWholeWitness (ctx : RuleContext) (u : WorldId) : Prop where
  «支持» : WholeWorldSupportWitness ctx u
  «无阻断» : ¬ WholeWorldBlocker ctx u

namespace IndependentWholeWitness

abbrev support {ctx : RuleContext} {u : WorldId} := @IndependentWholeWitness.«支持» ctx u
abbrev noBlock {ctx : RuleContext} {u : WorldId} := @IndependentWholeWitness.«无阻断» ctx u

end IndependentWholeWitness

def IndependentWholeWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : IndependentWholeWitness ctx u) :
    IndependentWhole ctx u :=
  ⟨w.support.proves, w.noBlock⟩

theorem independentWhole_iff_witness (ctx : RuleContext) (u : WorldId) :
    IndependentWhole ctx u ↔ IndependentWholeWitness ctx u := by
  constructor
  · intro h
    exact { «支持» := (wholeWorldSupport_iff_witness ctx u).mp h.1
          , «无阻断» := h.2 }
  · intro h
    exact h.proves

abbrev «独立整体见证» := IndependentWholeWitness
abbrev «独立整体当且仅当存在见证» := independentWhole_iff_witness

structure MonadicUniverseWitness (ctx : RuleContext) (u : WorldId) : Prop where
  «核心» : WorldCoreStructureWitness ctx u
  «整体» : IndependentWholeWitness ctx u

namespace MonadicUniverseWitness

abbrev core {ctx : RuleContext} {u : WorldId} := @MonadicUniverseWitness.«核心» ctx u
abbrev whole {ctx : RuleContext} {u : WorldId} := @MonadicUniverseWitness.«整体» ctx u

end MonadicUniverseWitness

def MonadicUniverseWitness.proves
    {ctx : RuleContext} {u : WorldId}
    (w : MonadicUniverseWitness ctx u) :
    IsMonadicUniverse ctx u :=
  ⟨w.core.proves, w.whole.proves⟩

theorem isMonadicUniverse_iff_witness (ctx : RuleContext) (u : WorldId) :
    IsMonadicUniverse ctx u ↔ MonadicUniverseWitness ctx u := by
  constructor
  · intro h
    exact { «核心» := (worldCoreStructure_iff_witness ctx u).mp h.1
          , «整体» := (independentWhole_iff_witness ctx u).mp h.2 }
  · intro h
    exact h.proves

abbrev «单体宇宙见证» := MonadicUniverseWitness
abbrev «单体宇宙当且仅当存在见证» := isMonadicUniverse_iff_witness

inductive WorldScaleWitness (ctx : RuleContext) (u : WorldId) :
    ArgumentProfile → Prop where
  | monadicSpatial (h : WorldFactWitness ctx u .hasSpatialInfinity) :
      WorldScaleWitness ctx u .monadicOnly
  | monadicTemporal (h : WorldFactWitness ctx u .hasTemporalInfinity) :
      WorldScaleWitness ctx u .monadicOnly
  | destructionQualified
      (hSpatial : WorldFactWitness ctx u .hasSpatialInfinity)
      (hTemporal : WorldFactWitness ctx u .hasTemporalInfinity) :
      WorldScaleWitness ctx u .destructionQualified

def WorldScaleWitness.proves
    {ctx : RuleContext} {u : WorldId} {profile : ArgumentProfile}
    (w : WorldScaleWitness ctx u profile) :
    MeetsWorldScalePolicy ctx profile u := by
  cases w with
  | monadicSpatial h => exact Or.inl h.proves
  | monadicTemporal h => exact Or.inr h.proves
  | destructionQualified hSpatial hTemporal => exact ⟨hSpatial.proves, hTemporal.proves⟩

theorem meetsWorldScalePolicy_iff_witness
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) :
    MeetsWorldScalePolicy ctx profile u ↔ WorldScaleWitness ctx u profile := by
  cases profile with
  | monadicOnly =>
      constructor
      · intro h
        rcases h with h | h
        · exact .monadicSpatial (.direct h)
        · exact .monadicTemporal (.direct h)
      · intro h
        exact h.proves
  | destructionQualified =>
      constructor
      · intro h
        exact .destructionQualified (.direct h.1) (.direct h.2)
      · intro h
        exact h.proves

abbrev «尺度要求见证» := WorldScaleWitness
abbrev «尺度要求当且仅当存在见证» := meetsWorldScalePolicy_iff_witness

structure MonadicArgumentWitness
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : Prop where
  «核心» : WorldCoreStructureWitness ctx u
  «尺度» : WorldScaleWitness ctx u profile

namespace MonadicArgumentWitness

abbrev core {ctx : RuleContext} {profile : ArgumentProfile} {u : WorldId} :=
  @MonadicArgumentWitness.«核心» ctx profile u
abbrev scale {ctx : RuleContext} {profile : ArgumentProfile} {u : WorldId} :=
  @MonadicArgumentWitness.«尺度» ctx profile u

end MonadicArgumentWitness

def MonadicArgumentWitness.proves
    {ctx : RuleContext} {profile : ArgumentProfile} {u : WorldId}
    (w : MonadicArgumentWitness ctx profile u) :
    SupportsMonadicArgument ctx profile u :=
  ⟨w.core.proves, w.scale.proves⟩

theorem supportsMonadicArgument_iff_witness
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) :
    SupportsMonadicArgument ctx profile u ↔
      MonadicArgumentWitness ctx profile u := by
  constructor
  · intro h
    exact { «核心» := (worldCoreStructure_iff_witness ctx u).mp h.1
          , «尺度» := (meetsWorldScalePolicy_iff_witness ctx profile u).mp h.2 }
  · intro h
    exact h.proves

abbrev «单体论证见证» := MonadicArgumentWitness
abbrev «单体论证当且仅当存在见证» := supportsMonadicArgument_iff_witness

end VerseFramework
