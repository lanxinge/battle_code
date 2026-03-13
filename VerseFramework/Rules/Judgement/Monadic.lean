import VerseFramework.Core.Argument
import VerseFramework.Rules.Bridge.Monadic

namespace VerseFramework

def «连通» (ctx : RuleContext) (u : WorldId) : Prop :=
  ctx.HasWorldFact u .connectedSpacetimeObject ∨
  (ctx.assumptions.allows .connectedFromCauchyLikeSlices ∧
    ctx.HasWorldFact u .hasCauchyLikeSlices ∧
    SpatialSupport ctx u ∧
    TemporalSupport ctx u)

abbrev Connected := «连通»

def «时空性» (ctx : RuleContext) (u : WorldId) : Prop :=
  «空间支持» ctx u ∧ «时间支持» ctx u

abbrev Spatiotemporal := «时空性»

def «自治世界动力学» (ctx : RuleContext) (u : WorldId) : Prop :=
  «自治演化支持» ctx u ∧ ¬ «动力学依赖阻断» ctx u

abbrev AutonomousWorldDynamics := «自治世界动力学»

def «动力统一» (ctx : RuleContext) (u : WorldId) : Prop :=
  «动力学支持» ctx u ∧ ¬ «动力学依赖阻断» ctx u

abbrev DynamicallyUnified := «动力统一»

def «世界核心结构» (ctx : RuleContext) (u : WorldId) : Prop :=
  «连通» ctx u ∧
  «时空性» ctx u ∧
  «动力统一» ctx u

abbrev WorldCoreStructure := «世界核心结构»

def «独立整体» (ctx : RuleContext) (u : WorldId) : Prop :=
  «完整世界支持» ctx u ∧ ¬ «完整世界阻断» ctx u

abbrev IndependentWhole := «独立整体»

def «是单体宇宙» (ctx : RuleContext) (u : WorldId) : Prop :=
  «世界核心结构» ctx u ∧
  «独立整体» ctx u

abbrev IsMonadicUniverse := «是单体宇宙»

theorem «单体判定当且仅当核心条件加完整世界性» (ctx : RuleContext) (u : WorldId) :
    «是单体宇宙» ctx u ↔
      «连通» ctx u ∧
      «时空性» ctx u ∧
      «动力统一» ctx u ∧
      «独立整体» ctx u := by
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

abbrev isMonadicUniverse_iff := «单体判定当且仅当核心条件加完整世界性»

theorem «单体成立可推出世界核心结构»
    {ctx : RuleContext} {u : WorldId}
    (h : «是单体宇宙» ctx u) :
    «世界核心结构» ctx u := by
  exact h.1

abbrev worldCoreStructure_of_isMonadicUniverse
    {ctx : RuleContext} {u : WorldId} :=
  @«单体成立可推出世界核心结构» ctx u

theorem «单体成立可推出单体候选»
    {ctx : RuleContext} {u : WorldId}
    (h : «是单体宇宙» ctx u) :
    «单体候选» ctx u := by
  exact ⟨h.1.2.1.1, h.1.2.1.2, h.1.2.2.1, h.2.1⟩

abbrev monadicCandidate_of_isMonadicUniverse
    {ctx : RuleContext} {u : WorldId} :=
  @«单体成立可推出单体候选» ctx u

theorem «不连通则不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (h : ¬ «连通» ctx u) :
    ¬ «是单体宇宙» ctx u := by
  intro hMono
  exact h hMono.1.1

abbrev not_isMonadicUniverse_of_not_connected
    {ctx : RuleContext} {u : WorldId} :=
  @«不连通则不能判为单体» ctx u

theorem «不具时空性则不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (h : ¬ «时空性» ctx u) :
    ¬ «是单体宇宙» ctx u := by
  intro hMono
  exact h hMono.1.2.1

abbrev not_isMonadicUniverse_of_not_spatiotemporal
    {ctx : RuleContext} {u : WorldId} :=
  @«不具时空性则不能判为单体» ctx u

theorem «动力不统一则不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (h : ¬ «动力统一» ctx u) :
    ¬ «是单体宇宙» ctx u := by
  intro hMono
  exact h hMono.1.2.2

abbrev not_isMonadicUniverse_of_not_dynamicallyUnified
    {ctx : RuleContext} {u : WorldId} :=
  @«动力不统一则不能判为单体» ctx u

theorem «不具完整世界性则不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (h : ¬ «独立整体» ctx u) :
    ¬ «是单体宇宙» ctx u := by
  intro hMono
  exact h hMono.2

abbrev not_isMonadicUniverse_of_not_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«不具完整世界性则不能判为单体» ctx u

theorem «仅框架对象不具完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (hFramework : ctx.HasWorldFact u .presentedAsFrameworkOnly) :
    ¬ «独立整体» ctx u := by
  intro hWhole
  exact hWhole.2 (Or.inr (Or.inr (Or.inr (Or.inl hFramework))))

abbrev frameworkOnly_not_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«仅框架对象不具完整世界性» ctx u

theorem «局部区域不具完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (hLocal : ctx.HasWorldFact u .presentedAsLocalRegion) :
    ¬ «独立整体» ctx u := by
  intro hWhole
  exact hWhole.2 (Or.inl hLocal)

abbrev localRegion_not_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«局部区域不具完整世界性» ctx u

theorem «口袋空间不具完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (hPocket : ctx.HasWorldFact u .presentedAsPocketSpace) :
    ¬ «独立整体» ctx u := by
  intro hWhole
  exact hWhole.2 (Or.inr (Or.inl hPocket))

abbrev pocketSpace_not_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«口袋空间不具完整世界性» ctx u

theorem «子系统不具完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (hSubsystem : ctx.HasWorldFact u .presentedAsSubsystem) :
    ¬ «独立整体» ctx u := by
  intro hWhole
  exact hWhole.2 (Or.inr (Or.inr (Or.inl hSubsystem)))

abbrev subsystem_not_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«子系统不具完整世界性» ctx u

theorem «索引族不具完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (hIndex : ctx.HasWorldFact u .presentedAsIndexFamily) :
    ¬ «独立整体» ctx u := by
  intro hWhole
  exact hWhole.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hIndex)))))

abbrev indexFamily_not_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«索引族不具完整世界性» ctx u

theorem «膜框架不具完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (hBrane : ctx.HasWorldFact u .presentedAsBraneFramework) :
    ¬ «独立整体» ctx u := by
  intro hWhole
  exact hWhole.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hBrane)))))

abbrev braneFramework_not_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«膜框架不具完整世界性» ctx u

theorem «仅框架对象不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (hFramework : ctx.HasWorldFact u .presentedAsFrameworkOnly) :
    ¬ «是单体宇宙» ctx u := by
  apply not_isMonadicUniverse_of_not_independentWhole
  exact frameworkOnly_not_independentWhole hFramework

abbrev not_isMonadicUniverse_of_frameworkOnly
    {ctx : RuleContext} {u : WorldId} :=
  @«仅框架对象不能判为单体» ctx u

theorem «局部区域不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (hLocal : ctx.HasWorldFact u .presentedAsLocalRegion) :
    ¬ «是单体宇宙» ctx u := by
  apply not_isMonadicUniverse_of_not_independentWhole
  exact localRegion_not_independentWhole hLocal

abbrev not_isMonadicUniverse_of_localRegion
    {ctx : RuleContext} {u : WorldId} :=
  @«局部区域不能判为单体» ctx u

theorem «口袋空间不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (hPocket : ctx.HasWorldFact u .presentedAsPocketSpace) :
    ¬ «是单体宇宙» ctx u := by
  apply not_isMonadicUniverse_of_not_independentWhole
  exact pocketSpace_not_independentWhole hPocket

abbrev not_isMonadicUniverse_of_pocketSpace
    {ctx : RuleContext} {u : WorldId} :=
  @«口袋空间不能判为单体» ctx u

theorem «子系统不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (hSubsystem : ctx.HasWorldFact u .presentedAsSubsystem) :
    ¬ «是单体宇宙» ctx u := by
  apply not_isMonadicUniverse_of_not_independentWhole
  exact subsystem_not_independentWhole hSubsystem

abbrev not_isMonadicUniverse_of_subsystem
    {ctx : RuleContext} {u : WorldId} :=
  @«子系统不能判为单体» ctx u

theorem «膜框架不能判为单体»
    {ctx : RuleContext} {u : WorldId}
    (hBrane : ctx.HasWorldFact u .presentedAsBraneFramework) :
    ¬ «是单体宇宙» ctx u := by
  apply not_isMonadicUniverse_of_not_independentWhole
  exact braneFramework_not_independentWhole hBrane

abbrev not_isMonadicUniverse_of_braneFramework
    {ctx : RuleContext} {u : WorldId} :=
  @«膜框架不能判为单体» ctx u

theorem «缺少完整世界支持则不具完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (hNoWhole : ¬ «完整世界支持» ctx u) :
    ¬ «独立整体» ctx u := by
  intro hWhole
  exact hNoWhole hWhole.1

abbrev not_independentWhole_of_no_wholeWorldSupport
    {ctx : RuleContext} {u : WorldId} :=
  @«缺少完整世界支持则不具完整世界性» ctx u

theorem «动力依赖阻断则不具动力统一性»
    {ctx : RuleContext} {u : WorldId}
    (hBlocked : «动力学依赖阻断» ctx u) :
    ¬ «动力统一» ctx u := by
  intro hDyn
  exact hDyn.2 hBlocked

abbrev not_dynamicallyUnified_of_dynamicsDependenceBlocker
    {ctx : RuleContext} {u : WorldId} :=
  @«动力依赖阻断则不具动力统一性» ctx u

theorem «动力统一可推出自主演化»
    {ctx : RuleContext} {u : WorldId}
    (hDyn : «动力统一» ctx u) :
    «自治世界动力学» ctx u := by
  exact ⟨hDyn.1.2, hDyn.2⟩

abbrev autonomousWorldDynamics_of_dynamicallyUnified
    {ctx : RuleContext} {u : WorldId} :=
  @«动力统一可推出自主演化» ctx u

theorem «仅连续统不足以给出完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (_hContinuum : ctx.HasWorldFact u .presentedAsContinuumOnly)
    (hNoWhole : ¬ «完整世界支持» ctx u) :
    ¬ «独立整体» ctx u := by
  exact not_independentWhole_of_no_wholeWorldSupport hNoWhole

abbrev continuumOnly_insufficient_for_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«仅连续统不足以给出完整世界性» ctx u

theorem «世界线结构不足以给出完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (_hWorldline : ctx.HasWorldFact u .presentedAsWorldlineStructure)
    (hNoWhole : ¬ «完整世界支持» ctx u) :
    ¬ «独立整体» ctx u := by
  exact not_independentWhole_of_no_wholeWorldSupport hNoWhole

abbrev worldlineStructure_insufficient_for_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«世界线结构不足以给出完整世界性» ctx u

theorem «希尔伯特空间不足以给出完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (_hHilbert : ctx.HasWorldFact u .presentedAsHilbertSpace)
    (hNoWhole : ¬ «完整世界支持» ctx u) :
    ¬ «独立整体» ctx u := by
  exact not_independentWhole_of_no_wholeWorldSupport hNoWhole

abbrev hilbertSpace_insufficient_for_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«希尔伯特空间不足以给出完整世界性» ctx u

theorem «相空间不足以给出完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (_hPhase : ctx.HasWorldFact u .presentedAsPhaseSpace)
    (hNoWhole : ¬ «完整世界支持» ctx u) :
    ¬ «独立整体» ctx u := by
  exact not_independentWhole_of_no_wholeWorldSupport hNoWhole

abbrev phaseSpace_insufficient_for_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«相空间不足以给出完整世界性» ctx u

theorem «配置空间不足以给出完整世界性»
    {ctx : RuleContext} {u : WorldId}
    (_hConfig : ctx.HasWorldFact u .presentedAsConfigurationSpace)
    (hNoWhole : ¬ «完整世界支持» ctx u) :
    ¬ «独立整体» ctx u := by
  exact not_independentWhole_of_no_wholeWorldSupport hNoWhole

abbrev configurationSpace_insufficient_for_independentWhole
    {ctx : RuleContext} {u : WorldId} :=
  @«配置空间不足以给出完整世界性» ctx u

theorem «纯空间背景不足以判单体»
    {ctx : RuleContext} {u : WorldId}
    (_hPure : ctx.HasWorldFact u .presentedAsPureSpace)
    (hNoTemporal : ¬ «时间支持» ctx u) :
    ¬ «时空性» ctx u := by
  intro hST
  exact hNoTemporal hST.2

abbrev pureSpace_background_insufficient
    {ctx : RuleContext} {u : WorldId} :=
  @«纯空间背景不足以判单体» ctx u

theorem «时空双无限可推出无限性见证»
    {ctx : RuleContext} {u : WorldId}
    (h : «时空无限性» ctx u) :
    «无限性见证» ctx u := by
  exact Or.inl h.1

abbrev spatiotemporalInfinity_implies_infinityWitness
    {ctx : RuleContext} {u : WorldId} :=
  @«时空双无限可推出无限性见证» ctx u

end VerseFramework
