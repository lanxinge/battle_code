import VerseFramework.Core.Theory
import VerseFramework.Rules.Monadic

namespace VerseFramework

def RuleContext.modelSemantics
    (ctx : RuleContext) (U : UniverseModel) :
    UniverseModelSemantics U :=
  { «连通时空整体» := Connected ctx U.«名称»
    «具有时空结构» := Spatiotemporal ctx U.«名称»
    «服从统一动力学» := DynamicsSupport ctx U.«名称»
    «整体边界演化» := AutonomousWorldDynamics ctx U.«名称»
    «具有合理状态类» := ctx.HasWorldFact U.«名称» .hasCauchyLikeSlices
    «被呈现为完整宇宙» := WholeWorldSupport ctx U.«名称»
    «被呈现为局部区域» := ctx.HasWorldFact U.«名称» .presentedAsLocalRegion
    «被呈现为口袋空间» := ctx.HasWorldFact U.«名称» .presentedAsPocketSpace
    «被呈现为子系统» := ctx.HasWorldFact U.«名称» .presentedAsSubsystem
    «被呈现为仅框架» := ctx.HasWorldFact U.«名称» .presentedAsFrameworkOnly
    «被呈现为索引族» := ctx.HasWorldFact U.«名称» .presentedAsIndexFamily
    «被呈现为膜框架» := ctx.HasWorldFact U.«名称» .presentedAsBraneFramework }

namespace «规则上下文»

abbrev «模型语义» := RuleContext.modelSemantics

end «规则上下文»

theorem modelIndependent_of_independentWhole
    {ctx : RuleContext} {U : UniverseModel}
    (h : IndependentWhole ctx U.name) :
    ModelIndependent (ctx.modelSemantics U) := by
  refine ⟨h.1, ?_⟩
  intro hBlock
  rcases hBlock with hLocal | hRest
  · exact h.2 (Or.inl hLocal)
  · rcases hRest with hPocket | hRest
    · exact h.2 (Or.inr (Or.inl hPocket))
    · rcases hRest with hSubsystem | hRest
      · exact h.2 (Or.inr (Or.inr (Or.inl hSubsystem)))
      · rcases hRest with hFramework | hRest
        · exact h.2 (Or.inr (Or.inr (Or.inr (Or.inl hFramework))))
        · rcases hRest with hIndex | hBrane
          · exact h.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hIndex)))))
          · exact h.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hBrane)))))

theorem isMonadicUniverseModel_of_isMonadicUniverse
    {ctx : RuleContext} {U : UniverseModel}
    (h : IsMonadicUniverse ctx U.name) :
    IsMonadicUniverseModel (ctx.modelSemantics U) := by
  refine ⟨?_, ?_, ?_, modelIndependent_of_independentWhole h.2⟩
  · exact h.1.1
  · exact h.1.2.1
  · exact ⟨h.1.2.2.1, autonomousWorldDynamics_of_dynamicallyUnified h.1.2.2⟩

abbrev «完整世界性可推出模型独立性»
    {ctx : RuleContext} {U : UniverseModel} :=
  @modelIndependent_of_independentWhole ctx U

abbrev «单体成立可推出单体宇宙模型»
    {ctx : RuleContext} {U : UniverseModel} :=
  @isMonadicUniverseModel_of_isMonadicUniverse ctx U

end VerseFramework
