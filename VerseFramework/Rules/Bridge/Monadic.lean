import VerseFramework.Rules.Context

namespace VerseFramework

def «空间支持» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .hasSpatialAspect ∨
  ctx.HasWorldFact u .connectedSpacetimeObject

abbrev SpatialSupport := «空间支持»

def «时间支持» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .hasTemporalAspect ∨
  ctx.HasWorldFact u .connectedSpacetimeObject ∨
  (ctx.assumptions.allows .temporalFromWorldHistory ∧
    ctx.HasWorldFact u .hasWorldHistory) ∨
  (ctx.assumptions.allows .weakRealistCosmology ∧
    ctx.HasWorldFact u .presentedInRealistPhysicsSetting ∧
    ctx.HasWorldFact u .hasSpatialAspect)

abbrev TemporalSupport := «时间支持»

def «自治演化支持» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .hasAutonomousEvolution ∨
  ctx.HasWorldFact u .hasUnifiedDynamics ∨
  (ctx.assumptions.allows .autonomousEvolutionFromHistory ∧
    ctx.HasWorldFact u .hasWorldHistory ∧
    ctx.HasWorldFact u .hasGlobalEvolution) ∨
  (ctx.assumptions.allows .weakRealistCosmology ∧
    ctx.HasWorldFact u .presentedInRealistPhysicsSetting ∧
    ctx.HasWorldFact u .hasWorldHistory)

abbrev AutonomousEvolutionSupport := «自治演化支持»

def «动力学依赖阻断» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .requiresExternalSustenance ∨
  ctx.HasWorldFact u .requiresExternalGovernance

abbrev DynamicsDependenceBlocker := «动力学依赖阻断»

def «动力学支持» (ctx : RuleContext) (u : WorldId) : Prop :=
  (ctx.HasWorldFact u .hasUnifiedDynamics ∨
  (ctx.assumptions.allows .unifiedDynamicsFromHistory ∧
    ctx.HasWorldFact u .hasWorldHistory ∧
    ctx.HasWorldFact u .hasGlobalEvolution) ∨
  (ctx.assumptions.allows .weakRealistCosmology ∧
    ctx.HasWorldFact u .presentedInRealistPhysicsSetting ∧
    ctx.HasWorldFact u .hasWorldHistory)) ∧
  «自治演化支持» ctx u

abbrev DynamicsSupport := «动力学支持»

def «完整世界支持» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .presentedAsWholeWorld ∨
  (ctx.assumptions.allows .wholeWorldFromExplicitUniverseLabel ∧
    ctx.HasWorldFact u .explicitlyCalledUniverse)

abbrev WholeWorldSupport := «完整世界支持»

def «完整世界阻断» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .presentedAsLocalRegion ∨
  ctx.HasWorldFact u .presentedAsPocketSpace ∨
  ctx.HasWorldFact u .presentedAsSubsystem ∨
  ctx.HasWorldFact u .presentedAsFrameworkOnly ∨
  ctx.HasWorldFact u .presentedAsIndexFamily ∨
  ctx.HasWorldFact u .presentedAsBraneFramework

abbrev WholeWorldBlocker := «完整世界阻断»

def «单体候选» (ctx : RuleContext) (u : WorldId) : Prop :=
  «空间支持» ctx u ∧
  «时间支持» ctx u ∧
  «动力学支持» ctx u ∧
  «完整世界支持» ctx u

abbrev MonadicCandidate := «单体候选»

def «空间无限支持» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .hasSpatialInfinity

abbrev SpatialInfinitySupport := «空间无限支持»

def «时间无限支持» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .hasTemporalInfinity

abbrev TemporalInfinitySupport := «时间无限支持»

def «无限性见证» (ctx : RuleContext) (u : WorldId) : Prop :=
  «空间无限支持» ctx u ∨
  «时间无限支持» ctx u

abbrev InfinityWitness := «无限性见证»

def «时空无限性» (ctx : RuleContext) (u : WorldId) : Prop :=
  «空间无限支持» ctx u ∧
  «时间无限支持» ctx u

abbrev SpatiotemporalInfinity := «时空无限性»

end VerseFramework
