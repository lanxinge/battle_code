import VerseFramework.Rules.Destruction
import VerseFramework.Rules.Witness.Common

namespace VerseFramework

inductive ExactDestructionLevelWitness
    (ctx : RuleContext) (aId : AttackId) : DestructionLevel → Prop where
  | factInstant (h : AttackFactWitness ctx aId .factInstantTotalDestruction) :
      ExactDestructionLevelWitness ctx aId .factInstant
  | factProcess (h : AttackFactWitness ctx aId .factProcessTotalDestruction) :
      ExactDestructionLevelWitness ctx aId .factProcess
  | necessaryPotential (h : AttackFactWitness ctx aId .necessaryPotentialTotalDestruction) :
      ExactDestructionLevelWitness ctx aId .necessaryPotential
  | conditionalPotential (h : AttackFactWitness ctx aId .conditionalPotentialTotalDestruction) :
      ExactDestructionLevelWitness ctx aId .conditionalPotential

def ExactDestructionLevelWitness.proves
    {ctx : RuleContext} {aId : AttackId} {lvl : DestructionLevel}
    (w : ExactDestructionLevelWitness ctx aId lvl) :
    ExactDestructionLevel ctx aId lvl := by
  cases w with
  | factInstant h => exact h.proves
  | factProcess h => exact h.proves
  | necessaryPotential h => exact h.proves
  | conditionalPotential h => exact h.proves

abbrev «精确毁灭层级见证» := ExactDestructionLevelWitness

theorem exactDestructionLevel_iff_witness
    (ctx : RuleContext) (aId : AttackId) (lvl : DestructionLevel) :
    ExactDestructionLevel ctx aId lvl ↔
      ExactDestructionLevelWitness ctx aId lvl := by
  cases lvl with
  | factInstant =>
      constructor
      · intro h
        exact .factInstant (.direct h)
      · intro h
        exact h.proves
  | factProcess =>
      constructor
      · intro h
        exact .factProcess (.direct h)
      · intro h
        exact h.proves
  | necessaryPotential =>
      constructor
      · intro h
        exact .necessaryPotential (.direct h)
      · intro h
        exact h.proves
  | conditionalPotential =>
      constructor
      · intro h
        exact .conditionalPotential (.direct h)
      · intro h
        exact h.proves

abbrev «精确毁灭层级当且仅当存在见证» := exactDestructionLevel_iff_witness

inductive AttackAtLeastWitness
    (ctx : RuleContext) (aId : AttackId) (lvl : DestructionLevel) : Prop where
  | mk
      (exact : DestructionLevel)
      (support : ExactDestructionLevelWitness ctx aId exact)
      (order : exact.StrongerOrEqual lvl) :
      AttackAtLeastWitness ctx aId lvl

def AttackAtLeastWitness.proves
    {ctx : RuleContext} {aId : AttackId} {lvl : DestructionLevel}
    (w : AttackAtLeastWitness ctx aId lvl) :
    AttackAtLeast ctx aId lvl := by
  cases w with
  | mk exact support order =>
      exact ⟨exact, support.proves, order⟩

abbrev «攻击至少达到见证» := AttackAtLeastWitness

theorem attackAtLeast_iff_witness
    (ctx : RuleContext) (aId : AttackId) (lvl : DestructionLevel) :
    AttackAtLeast ctx aId lvl ↔ AttackAtLeastWitness ctx aId lvl := by
  constructor
  · intro h
    rcases h with ⟨exact, hExact, hOrder⟩
    exact .mk exact ((exactDestructionLevel_iff_witness ctx aId exact).mp hExact) hOrder
  · intro h
    exact h.proves

abbrev «攻击至少达到当且仅当存在见证» := attackAtLeast_iff_witness

end VerseFramework
