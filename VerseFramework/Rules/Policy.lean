import VerseFramework.Rules.Judgement.Monadic

namespace VerseFramework

def «满足尺度要求» (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : Prop :=
  match profile with
  | .monadicOnly => «无限性见证» ctx u
  | .destructionQualified => «时空无限性» ctx u

abbrev MeetsWorldScalePolicy := «满足尺度要求»

@[simp] theorem «单体档尺度要求等价于无限性见证»
    (ctx : RuleContext) (u : WorldId) :
    «满足尺度要求» ctx .monadicOnly u ↔ «无限性见证» ctx u := by
  rfl

abbrev meetsWorldScalePolicy_monadicOnly := «单体档尺度要求等价于无限性见证»

@[simp] theorem «破坏量级档尺度要求等价于时空双无限»
    (ctx : RuleContext) (u : WorldId) :
    «满足尺度要求» ctx .destructionQualified u ↔ «时空无限性» ctx u := by
  rfl

abbrev meetsWorldScalePolicy_destructionQualified := «破坏量级档尺度要求等价于时空双无限»

def «可用于单体论证» (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : Prop :=
  «世界核心结构» ctx u ∧ «满足尺度要求» ctx profile u

abbrev SupportsMonadicArgument := «可用于单体论证»

theorem «破坏量级档可推出单体档»
    {ctx : RuleContext} {u : WorldId}
    (h : «可用于单体论证» ctx .destructionQualified u) :
    «可用于单体论证» ctx .monadicOnly u := by
  exact ⟨h.1, Or.inl h.2.1⟩

abbrev supportsMonadicArgument_monadicOnly_of_destructionQualified
    {ctx : RuleContext} {u : WorldId} :=
  @«破坏量级档可推出单体档» ctx u

theorem «世界核心结构加无限性即可用于单体论证»
    {ctx : RuleContext} {u : WorldId}
    (hCore : «世界核心结构» ctx u)
    (hScale : «无限性见证» ctx u) :
    «可用于单体论证» ctx .monadicOnly u := by
  exact ⟨hCore, hScale⟩

abbrev supportsMonadicArgument_of_worldCore_and_infinityWitness
    {ctx : RuleContext} {u : WorldId} :=
  @«世界核心结构加无限性即可用于单体论证» ctx u

theorem «世界核心结构加时空双无限即可用于破坏量级论证»
    {ctx : RuleContext} {u : WorldId}
    (hCore : «世界核心结构» ctx u)
    (hScale : «时空无限性» ctx u) :
    «可用于单体论证» ctx .destructionQualified u := by
  exact ⟨hCore, hScale⟩

abbrev supportsMonadicArgument_of_worldCore_and_spatiotemporalInfinity
    {ctx : RuleContext} {u : WorldId} :=
  @«世界核心结构加时空双无限即可用于破坏量级论证» ctx u

end VerseFramework
