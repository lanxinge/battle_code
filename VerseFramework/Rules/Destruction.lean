import VerseFramework.Core.Destruction
import VerseFramework.Rules.Context

namespace VerseFramework

def «精确毁灭层级» (ctx : RuleContext) (a : AttackId) :
    DestructionLevel → Prop
  | .factInstant => ctx.HasAttackFact a .factInstantTotalDestruction
  | .factProcess => ctx.HasAttackFact a .factProcessTotalDestruction
  | .necessaryPotential => ctx.HasAttackFact a .necessaryPotentialTotalDestruction
  | .conditionalPotential => ctx.HasAttackFact a .conditionalPotentialTotalDestruction

abbrev ExactDestructionLevel := «精确毁灭层级»

def «攻击至少达到» (ctx : RuleContext) (a : AttackId) (lvl : DestructionLevel) : Prop :=
  ∃ exact, «精确毁灭层级» ctx a exact ∧ exact.StrongerOrEqual lvl

abbrev AttackAtLeast := «攻击至少达到»

theorem «精确事态可推出至少同级事态»
    {ctx : RuleContext} {a : AttackId} {lvl : DestructionLevel}
    (h : «精确毁灭层级» ctx a lvl) :
    «攻击至少达到» ctx a lvl := by
  exact ⟨lvl, h, DestructionLevel.strongerOrEqual_refl lvl⟩

abbrev attackAtLeast_of_exact
    {ctx : RuleContext} {a : AttackId} {lvl : DestructionLevel} :=
  @«精确事态可推出至少同级事态» ctx a lvl

theorem «事实瞬时可推出至少事实过程»
    {ctx : RuleContext} {a : AttackId}
    (h : «精确毁灭层级» ctx a .factInstant) :
    «攻击至少达到» ctx a .factProcess := by
  exact ⟨.factInstant, h, DestructionLevel.factInstant_strongerOrEqual_factProcess⟩

abbrev attackAtLeast_factProcess_of_factInstant
    {ctx : RuleContext} {a : AttackId} :=
  @«事实瞬时可推出至少事实过程» ctx a

theorem «事实瞬时可推出至少必然潜能»
    {ctx : RuleContext} {a : AttackId}
    (h : «精确毁灭层级» ctx a .factInstant) :
    «攻击至少达到» ctx a .necessaryPotential := by
  exact ⟨.factInstant, h, DestructionLevel.factInstant_strongerOrEqual_necessaryPotential⟩

abbrev attackAtLeast_necessaryPotential_of_factInstant
    {ctx : RuleContext} {a : AttackId} :=
  @«事实瞬时可推出至少必然潜能» ctx a

theorem «事实瞬时可推出至少条件潜能»
    {ctx : RuleContext} {a : AttackId}
    (h : «精确毁灭层级» ctx a .factInstant) :
    «攻击至少达到» ctx a .conditionalPotential := by
  exact ⟨.factInstant, h, DestructionLevel.factInstant_strongerOrEqual_conditionalPotential⟩

abbrev attackAtLeast_conditionalPotential_of_factInstant
    {ctx : RuleContext} {a : AttackId} :=
  @«事实瞬时可推出至少条件潜能» ctx a

theorem «事实过程可推出至少必然潜能»
    {ctx : RuleContext} {a : AttackId}
    (h : «精确毁灭层级» ctx a .factProcess) :
    «攻击至少达到» ctx a .necessaryPotential := by
  exact ⟨.factProcess, h, DestructionLevel.factProcess_strongerOrEqual_necessaryPotential⟩

abbrev attackAtLeast_necessaryPotential_of_factProcess
    {ctx : RuleContext} {a : AttackId} :=
  @«事实过程可推出至少必然潜能» ctx a

theorem «事实过程可推出至少条件潜能»
    {ctx : RuleContext} {a : AttackId}
    (h : «精确毁灭层级» ctx a .factProcess) :
    «攻击至少达到» ctx a .conditionalPotential := by
  exact ⟨.factProcess, h, DestructionLevel.factProcess_strongerOrEqual_conditionalPotential⟩

abbrev attackAtLeast_conditionalPotential_of_factProcess
    {ctx : RuleContext} {a : AttackId} :=
  @«事实过程可推出至少条件潜能» ctx a

theorem «必然潜能可推出至少条件潜能»
    {ctx : RuleContext} {a : AttackId}
    (h : «精确毁灭层级» ctx a .necessaryPotential) :
    «攻击至少达到» ctx a .conditionalPotential := by
  exact ⟨.necessaryPotential, h, DestructionLevel.necessaryPotential_strongerOrEqual_conditionalPotential⟩

abbrev attackAtLeast_conditionalPotential_of_necessaryPotential
    {ctx : RuleContext} {a : AttackId} :=
  @«必然潜能可推出至少条件潜能» ctx a

theorem «条件潜能不足以推出事实过程» :
    ¬ DestructionLevel.StrongerOrEqual .conditionalPotential .factProcess := by
  exact DestructionLevel.conditionalPotential_not_strongerOrEqual_factProcess

abbrev conditionalPotential_insufficient_for_factProcess := «条件潜能不足以推出事实过程»

end VerseFramework
