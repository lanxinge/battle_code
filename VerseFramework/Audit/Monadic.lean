import VerseFramework.Core.Claim
import VerseFramework.Audit.Common
import VerseFramework.Rules.Monadic

namespace VerseFramework

structure WorldCoreAudit where
  «世界» : WorldId
  «连通» : ConditionAudit
  «时空» : ConditionAudit
  «动力学» : ConditionAudit
  deriving Repr

abbrev «世界核心审计» := WorldCoreAudit

namespace WorldCoreAudit

abbrev world := WorldCoreAudit.«世界»
abbrev connected := WorldCoreAudit.«连通»
abbrev spatiotemporal := WorldCoreAudit.«时空»
abbrev dynamics := WorldCoreAudit.«动力学»

def items (audit : WorldCoreAudit) : List ConditionAudit :=
  [audit.connected, audit.spatiotemporal, audit.dynamics]

def proofStatus (audit : WorldCoreAudit) : ProofStatus :=
  ProofStatus.merge (audit.items.map ConditionAudit.proofStatus)

def renderLines (audit : WorldCoreAudit) : List String :=
  [ s!"WorldCore: {audit.world}"
  , s!"ProofStatus: {reprStr audit.proofStatus}" ] ++
  audit.connected.renderLines ++
  audit.spatiotemporal.renderLines ++
  audit.dynamics.renderLines

end WorldCoreAudit

namespace «世界核心审计»

abbrev «世界» := WorldCoreAudit.«世界»
abbrev «连通» := WorldCoreAudit.«连通»
abbrev «时空» := WorldCoreAudit.«时空»
abbrev «动力学» := WorldCoreAudit.«动力学»
abbrev «条目» := WorldCoreAudit.items
abbrev «证明状态» := WorldCoreAudit.proofStatus
abbrev «渲染行» := WorldCoreAudit.renderLines

end «世界核心审计»

structure MonadicUniverseAudit where
  «世界» : WorldId
  «核心» : WorldCoreAudit
  «独立整体» : ConditionAudit
  deriving Repr

abbrev «单体宇宙审计» := MonadicUniverseAudit

namespace MonadicUniverseAudit

abbrev world := MonadicUniverseAudit.«世界»
abbrev core := MonadicUniverseAudit.«核心»
abbrev independentWhole := MonadicUniverseAudit.«独立整体»

def proofStatus (audit : MonadicUniverseAudit) : ProofStatus :=
  ProofStatus.merge
    [audit.core.proofStatus, audit.independentWhole.proofStatus]

def verdict (audit : MonadicUniverseAudit) : Verdict Claim :=
  { «断言» := .monadicUniverse audit.world
    «状态» := audit.proofStatus }

def renderLines (audit : MonadicUniverseAudit) : List String :=
  [ s!"Claim: monadic universe ({audit.world})"
  , s!"ProofStatus: {reprStr audit.proofStatus}" ] ++
  audit.core.connected.renderLines ++
  audit.core.spatiotemporal.renderLines ++
  audit.core.dynamics.renderLines ++
  audit.independentWhole.renderLines

end MonadicUniverseAudit

namespace «单体宇宙审计»

abbrev «世界» := MonadicUniverseAudit.«世界»
abbrev «核心» := MonadicUniverseAudit.«核心»
abbrev «独立整体» := MonadicUniverseAudit.«独立整体»
abbrev «证明状态» := MonadicUniverseAudit.proofStatus
abbrev «判定» := MonadicUniverseAudit.verdict
abbrev «渲染行» := MonadicUniverseAudit.renderLines

end «单体宇宙审计»

structure MonadicArgumentAudit where
  «世界» : WorldId
  «配置» : ArgumentProfile
  «核心» : WorldCoreAudit
  «尺度» : ConditionAudit
  «整体世界» : ConditionAudit
  deriving Repr

abbrev «单体论证审计» := MonadicArgumentAudit

namespace MonadicArgumentAudit

abbrev world := MonadicArgumentAudit.«世界»
abbrev profile := MonadicArgumentAudit.«配置»
abbrev core := MonadicArgumentAudit.«核心»
abbrev scale := MonadicArgumentAudit.«尺度»
abbrev wholeWorld := MonadicArgumentAudit.«整体世界»

def proofStatus (audit : MonadicArgumentAudit) : ProofStatus :=
  ProofStatus.merge [audit.core.proofStatus, audit.scale.proofStatus]

def strictComparisonStatus (audit : MonadicArgumentAudit) : ProofStatus :=
  ProofStatus.merge [audit.core.proofStatus, audit.scale.proofStatus, audit.wholeWorld.proofStatus]

def verdict (audit : MonadicArgumentAudit) : Verdict Claim :=
  { «断言» := .monadicArgument audit.world audit.profile
    «状态» := audit.proofStatus }

def renderLines (audit : MonadicArgumentAudit) : List String :=
  [ s!"Claim: monadic argument ({audit.world}, {reprStr audit.profile})"
  , s!"ArgumentStatus: {reprStr audit.proofStatus}"
  , s!"StrictComparisonStatus: {reprStr audit.strictComparisonStatus}"
  , "Whole-world is advisory here; it is surfaced for audit comparison, not as an argument-layer requirement." ] ++
  audit.core.connected.renderLines ++
  audit.core.spatiotemporal.renderLines ++
  audit.core.dynamics.renderLines ++
  audit.scale.renderLines ++
  audit.wholeWorld.renderLines

end MonadicArgumentAudit

namespace «单体论证审计»

abbrev «世界» := MonadicArgumentAudit.«世界»
abbrev «配置» := MonadicArgumentAudit.«配置»
abbrev «核心» := MonadicArgumentAudit.«核心»
abbrev «尺度» := MonadicArgumentAudit.«尺度»
abbrev «整体世界» := MonadicArgumentAudit.«整体世界»
abbrev «证明状态» := MonadicArgumentAudit.proofStatus
abbrev «严格比较状态» := MonadicArgumentAudit.strictComparisonStatus
abbrev «判定» := MonadicArgumentAudit.verdict
abbrev «渲染行» := MonadicArgumentAudit.renderLines

end «单体论证审计»

namespace RuleContext

noncomputable def worldBlockerNotes (ctx : RuleContext) (u : WorldId) : List String := by
  classical
  let localNotes :=
    if h : ctx.HasWorldFact u .presentedAsLocalRegion then
      "Blocked by local-region presentation." :: ctx.WorldAuditTrail u .presentedAsLocalRegion
    else []
  let pocketNotes :=
    if h : ctx.HasWorldFact u .presentedAsPocketSpace then
      "Blocked by pocket-space presentation." :: ctx.WorldAuditTrail u .presentedAsPocketSpace
    else []
  let subsystemNotes :=
    if h : ctx.HasWorldFact u .presentedAsSubsystem then
      "Blocked by subsystem presentation." :: ctx.WorldAuditTrail u .presentedAsSubsystem
    else []
  let frameworkNotes :=
    if h : ctx.HasWorldFact u .presentedAsFrameworkOnly then
      "Blocked by framework-only presentation." :: ctx.WorldAuditTrail u .presentedAsFrameworkOnly
    else []
  let indexNotes :=
    if h : ctx.HasWorldFact u .presentedAsIndexFamily then
      "Blocked by index-family presentation." :: ctx.WorldAuditTrail u .presentedAsIndexFamily
    else []
  let braneNotes :=
    if h : ctx.HasWorldFact u .presentedAsBraneFramework then
      "Blocked by brane/bulk framework presentation." :: ctx.WorldAuditTrail u .presentedAsBraneFramework
    else []
  exact localNotes ++ pocketNotes ++ subsystemNotes ++ frameworkNotes ++ indexNotes ++ braneNotes

noncomputable def negativeObjectNotes (ctx : RuleContext) (u : WorldId) : List String := by
  classical
  let pureSpaceNotes :=
    if h : ctx.HasWorldFact u .presentedAsPureSpace then
      "Negative profile: pure space alone does not establish a spacetime world." ::
        ctx.WorldAuditTrail u .presentedAsPureSpace
    else []
  let continuumNotes :=
    if h : ctx.HasWorldFact u .presentedAsContinuumOnly then
      "Negative profile: a continuum or R^n-like carrier does not by itself establish a world or multiverse." ::
        ctx.WorldAuditTrail u .presentedAsContinuumOnly
    else []
  let worldlineNotes :=
    if h : ctx.HasWorldFact u .presentedAsWorldlineStructure then
      "Negative profile: a worldline or worldline-family is world-internal structure, not a whole world by default." ::
        ctx.WorldAuditTrail u .presentedAsWorldlineStructure
    else []
  let hilbertNotes :=
    if h : ctx.HasWorldFact u .presentedAsHilbertSpace then
      "Negative profile: a Hilbert space is a state space, not automatically a universe object." ::
        ctx.WorldAuditTrail u .presentedAsHilbertSpace
    else []
  let phaseNotes :=
    if h : ctx.HasWorldFact u .presentedAsPhaseSpace then
      "Negative profile: a phase space is a state-space formalism, not automatically a universe object." ::
        ctx.WorldAuditTrail u .presentedAsPhaseSpace
    else []
  let configurationNotes :=
    if h : ctx.HasWorldFact u .presentedAsConfigurationSpace then
      "Negative profile: a configuration space is not automatically a whole world." ::
        ctx.WorldAuditTrail u .presentedAsConfigurationSpace
    else []
  exact pureSpaceNotes ++ continuumNotes ++ worldlineNotes ++ hilbertNotes ++ phaseNotes ++ configurationNotes

noncomputable def worldDynamicsDependencyNotes (ctx : RuleContext) (u : WorldId) : List String := by
  classical
  let sustenanceNotes :=
    if h : ctx.HasWorldFact u .requiresExternalSustenance then
      "Blocked by external sustenance: the world's ongoing evolution depends on an outside system." ::
        ctx.WorldAuditTrail u .requiresExternalSustenance
    else []
  let governanceNotes :=
    if h : ctx.HasWorldFact u .requiresExternalGovernance then
      "Blocked by external governance: the world's state transitions are controlled by an outside system." ::
        ctx.WorldAuditTrail u .requiresExternalGovernance
    else []
  exact sustenanceNotes ++ governanceNotes

end RuleContext

noncomputable def connectedAudit (ctx : RuleContext) (u : WorldId) : ConditionAudit := by
  classical
  if hDirect : ctx.HasWorldFact u .connectedSpacetimeObject then
    exact
      { «标签» := "Connected"
        «来源» := .directText
        «注记» := ctx.WorldAuditTrail u .connectedSpacetimeObject }
  else if hBridge :
      ctx.assumptions.allows .connectedFromCauchyLikeSlices ∧
      ctx.HasWorldFact u .hasCauchyLikeSlices ∧
      SpatialSupport ctx u ∧
      TemporalSupport ctx u then
    exact
      { «标签» := "Connected"
        «来源» := .bridgeWithAssumptions .connectedFromCauchyLikeSlices ctx.assumptions.name
        «注记» :=
          [ "Bridge: connectedness inferred from slice-like world states plus spatial and temporal support." ]
          ++ ctx.WorldAuditTrail u .hasCauchyLikeSlices }
  else
    exact
      { «标签» := "Connected"
        «来源» := .missing
        «注记» :=
          [ "Missing direct connected-spacetime support, and no enabled bridge from slice structure applies." ] }

noncomputable def spatiotemporalAudit (ctx : RuleContext) (u : WorldId) : ConditionAudit := by
  classical
  if hConnected : ctx.HasWorldFact u .connectedSpacetimeObject then
    exact
      { «标签» := "Spatiotemporal"
        «来源» := .directText
        «注记» := ctx.WorldAuditTrail u .connectedSpacetimeObject }
  else if hDirect :
      ctx.HasWorldFact u .hasSpatialAspect ∧
      ctx.HasWorldFact u .hasTemporalAspect then
    exact
      { «标签» := "Spatiotemporal"
        «来源» := .directText
        «注记» := ctx.WorldAuditTrail u .hasSpatialAspect ++ ctx.WorldAuditTrail u .hasTemporalAspect }
  else if hHistoryBridge :
      SpatialSupport ctx u ∧
      ctx.assumptions.allows .temporalFromWorldHistory ∧
      ctx.HasWorldFact u .hasWorldHistory then
    exact
      { «标签» := "Spatiotemporal"
        «来源» := .bridgeWithAssumptions .temporalFromWorldHistory ctx.assumptions.name
        «注记» :=
          [ "Bridge: temporal structure inferred from world-history under the active assumption pack." ]
          ++ ctx.WorldAuditTrail u .hasSpatialAspect
          ++ ctx.WorldAuditTrail u .hasWorldHistory }
  else if hRealistBridge :
      ctx.assumptions.allows .weakRealistCosmology ∧
      ctx.HasWorldFact u .presentedInRealistPhysicsSetting ∧
      ctx.HasWorldFact u .hasSpatialAspect then
    exact
      { «标签» := "Spatiotemporal"
        «来源» := .bridgeWithAssumptions
          .temporalFromRealistPhysicsSetting
          ctx.assumptions.name
        «注记» :=
          [ "Bridge: temporal structure inferred from a realist-physics setting under the active assumption pack." ]
          ++ ctx.WorldAuditTrail u .presentedInRealistPhysicsSetting
          ++ ctx.WorldAuditTrail u .hasSpatialAspect }
  else
    exact
      { «标签» := "Spatiotemporal"
        «来源» := .missing
        «注记» :=
          [ "Missing enough evidence to establish both spatial and temporal structure." ]
          ++ ctx.negativeObjectNotes u }

noncomputable def autonomousEvolutionAudit (ctx : RuleContext) (u : WorldId) : ConditionAudit := by
  classical
  if hBlocked : DynamicsDependenceBlocker ctx u then
    exact
      { «标签» := "AutonomousEvolution"
        «来源» := .blocked
        «注记» := ctx.worldDynamicsDependencyNotes u }
  else if hDirect : ctx.HasWorldFact u .hasAutonomousEvolution then
    exact
      { «标签» := "AutonomousEvolution"
        «来源» := .directText
        «注记» := ctx.WorldAuditTrail u .hasAutonomousEvolution }
  else if hUnified : ctx.HasWorldFact u .hasUnifiedDynamics then
    exact
      { «标签» := "AutonomousEvolution"
        «来源» := .bridge .autonomousEvolutionFromUnifiedDynamics
        «注记» :=
          [ "Direct unified-dynamics evidence is treated as autonomous world evolution unless explicit blockers are present." ]
          ++ ctx.WorldAuditTrail u .hasUnifiedDynamics }
  else if hHistoryBridge :
      ctx.assumptions.allows .autonomousEvolutionFromHistory ∧
      ctx.HasWorldFact u .hasWorldHistory ∧
      ctx.HasWorldFact u .hasGlobalEvolution then
    exact
      { «标签» := "AutonomousEvolution"
        «来源» := .bridgeWithAssumptions
          .autonomousEvolutionFromWorldHistory
          ctx.assumptions.name
        «注记» :=
          [ "Bridge: autonomous evolution inferred from one world-history plus global evolution." ]
          ++ ctx.WorldAuditTrail u .hasWorldHistory
          ++ ctx.WorldAuditTrail u .hasGlobalEvolution }
  else if hRealistBridge :
      ctx.assumptions.allows .weakRealistCosmology ∧
      ctx.HasWorldFact u .presentedInRealistPhysicsSetting ∧
      ctx.HasWorldFact u .hasWorldHistory then
    exact
      { «标签» := "AutonomousEvolution"
        «来源» := .bridgeWithAssumptions
          .autonomousEvolutionFromRealistPhysicsSetting
          ctx.assumptions.name
        «注记» :=
          [ "Bridge: weak realist-sf cosmology used to supply autonomous world evolution." ]
          ++ ctx.WorldAuditTrail u .presentedInRealistPhysicsSetting
          ++ ctx.WorldAuditTrail u .hasWorldHistory }
  else
    exact
      { «标签» := "AutonomousEvolution"
        «来源» := .missing
        «注记» :=
          [ "Missing enough evidence that the world's own evolution can proceed without ongoing external support or control." ] }

noncomputable def dynamicsAudit (ctx : RuleContext) (u : WorldId) : ConditionAudit := by
  classical
  if hBlocked : DynamicsDependenceBlocker ctx u then
    exact
      { «标签» := "DynamicallyUnified"
        «来源» := .blocked
        «注记» := ctx.worldDynamicsDependencyNotes u }
  else if hDirect : ctx.HasWorldFact u .hasUnifiedDynamics then
    exact
      { «标签» := "DynamicallyUnified"
        «来源» := .directText
        «注记» :=
          [ "Direct unified-dynamics evidence also counts as autonomous world evolution unless explicit blockers are present." ]
          ++ ctx.WorldAuditTrail u .hasUnifiedDynamics }
  else if hHistoryBridge :
      ctx.assumptions.allows .unifiedDynamicsFromHistory ∧
      ctx.assumptions.allows .autonomousEvolutionFromHistory ∧
      ctx.HasWorldFact u .hasWorldHistory ∧
      ctx.HasWorldFact u .hasGlobalEvolution then
    exact
      { «标签» := "DynamicallyUnified"
        «来源» := .bridgeWithAssumptions
          .unifiedDynamicsFromWorldHistory
          ctx.assumptions.name
        «注记» :=
          [ "Bridge: unified and autonomous world dynamics inferred from one world-history plus global evolution." ]
          ++ ctx.WorldAuditTrail u .hasWorldHistory
          ++ ctx.WorldAuditTrail u .hasGlobalEvolution }
  else if hRealistBridge :
      ctx.assumptions.allows .weakRealistCosmology ∧
      ctx.HasWorldFact u .presentedInRealistPhysicsSetting ∧
      ctx.HasWorldFact u .hasWorldHistory then
    exact
      { «标签» := "DynamicallyUnified"
        «来源» := .bridgeWithAssumptions
          .unifiedDynamicsFromRealistPhysicsSetting
          ctx.assumptions.name
        «注记» :=
          [ "Bridge: weak realist-sf cosmology used to supply unified dynamics." ]
          ++ ctx.WorldAuditTrail u .presentedInRealistPhysicsSetting
          ++ ctx.WorldAuditTrail u .hasWorldHistory }
  else if hAutonomyOnly : ctx.HasWorldFact u .hasAutonomousEvolution then
    exact
      { «标签» := "DynamicallyUnified"
        «来源» := .missing
        «注记» :=
          [ "Autonomous evolution alone is not yet enough; the text still needs unified world-dynamics support." ]
          ++ ctx.WorldAuditTrail u .hasAutonomousEvolution }
  else
    exact
      { «标签» := "DynamicallyUnified"
        «来源» := .missing
        «注记» :=
          [ "Missing enough evidence for unified and autonomous world dynamics, and no enabled bridge applies." ]
          ++ ctx.negativeObjectNotes u }

noncomputable def independentWholeAudit (ctx : RuleContext) (u : WorldId) : ConditionAudit := by
  classical
  if hBlocked : WholeWorldBlocker ctx u then
    exact
      { «标签» := "IndependentWhole"
        «来源» := .blocked
        «注记» := ctx.worldBlockerNotes u }
  else if hDirect : ctx.HasWorldFact u .presentedAsWholeWorld then
    exact
      { «标签» := "IndependentWhole"
        «来源» := .directText
        «注记» := ctx.WorldAuditTrail u .presentedAsWholeWorld }
  else if hBridge :
      ctx.assumptions.allows .wholeWorldFromExplicitUniverseLabel ∧
      ctx.HasWorldFact u .explicitlyCalledUniverse then
    exact
      { «标签» := "IndependentWhole"
        «来源» := .bridgeWithAssumptions
          .wholeWorldFromExplicitUniverseLabel
          ctx.assumptions.name
        «注记» :=
          [ "Bridge: whole-world status inferred from an explicit universe label." ]
          ++ ctx.WorldAuditTrail u .explicitlyCalledUniverse }
  else
    exact
      { «标签» := "IndependentWhole"
        «来源» := .missing
        «注记» :=
          [ "Missing a whole-world presentation, and no enabled label-based bridge applies." ]
          ++ ctx.negativeObjectNotes u }

noncomputable def argumentProfileAudit
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : ConditionAudit := by
  classical
  match profile with
  | .monadicOnly =>
      if hSpatial : SpatialInfinitySupport ctx u then
        exact
          { «标签» := "MonadicArgumentScale"
            «来源» := .directText
            «注记» :=
              [ "Monadic-only profile satisfied by spatial infinity." ]
              ++ ctx.WorldAuditTrail u .hasSpatialInfinity }
      else if hTemporal : TemporalInfinitySupport ctx u then
        exact
          { «标签» := "MonadicArgumentScale"
            «来源» := .directText
            «注记» :=
              [ "Monadic-only profile satisfied by temporal infinity." ]
              ++ ctx.WorldAuditTrail u .hasTemporalInfinity }
      else
        exact
          { «标签» := "MonadicArgumentScale"
            «来源» := .missing
            «注记» :=
              [ "Need either spatial infinity or temporal infinity for a standalone monadic argument." ] }
  | .destructionQualified =>
      if hBoth : SpatiotemporalInfinity ctx u then
        exact
          { «标签» := "DestructionQualifiedScale"
            «来源» := .directText
            «注记» :=
              [ "Destruction-qualified profile satisfied by full spatiotemporal infinity." ]
              ++ ctx.WorldAuditTrail u .hasSpatialInfinity
              ++ ctx.WorldAuditTrail u .hasTemporalInfinity }
      else
        exact
          { «标签» := "DestructionQualifiedScale"
            «来源» := .missing
            «注记» :=
              [ "Need both spatial infinity and temporal infinity before attaching destruction-scale claims." ] }

noncomputable def worldCoreAudit (ctx : RuleContext) (u : WorldId) : WorldCoreAudit :=
  { «世界» := u
    «连通» := connectedAudit ctx u
    «时空» := spatiotemporalAudit ctx u
    «动力学» := dynamicsAudit ctx u }

noncomputable def monadicUniverseAudit (ctx : RuleContext) (u : WorldId) : MonadicUniverseAudit :=
  { «世界» := u
    «核心» := worldCoreAudit ctx u
    «独立整体» := independentWholeAudit ctx u }

noncomputable def monadicArgumentAudit
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : MonadicArgumentAudit :=
  { «世界» := u
    «配置» := profile
    «核心» := worldCoreAudit ctx u
    «尺度» := argumentProfileAudit ctx profile u
    «整体世界» := independentWholeAudit ctx u }

noncomputable def monadicUniverseVerdict (ctx : RuleContext) (u : WorldId) : Verdict Claim :=
  (monadicUniverseAudit ctx u).verdict

noncomputable def monadicArgumentVerdict
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : Verdict Claim :=
  (monadicArgumentAudit ctx profile u).verdict

noncomputable abbrev «连通审计» := connectedAudit
noncomputable abbrev «时空审计» := spatiotemporalAudit
noncomputable abbrev «自治演化审计» := autonomousEvolutionAudit
noncomputable abbrev «动力学审计» := dynamicsAudit
noncomputable abbrev «独立整体审计» := independentWholeAudit
noncomputable abbrev «论证配置审计» := argumentProfileAudit
noncomputable abbrev «单体宇宙判定» := monadicUniverseVerdict
noncomputable abbrev «单体论证判定» := monadicArgumentVerdict

end VerseFramework
