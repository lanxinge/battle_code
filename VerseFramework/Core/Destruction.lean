namespace VerseFramework

inductive DestructionLevel where
  | factInstant
  | factProcess
  | necessaryPotential
  | conditionalPotential
  deriving DecidableEq, Repr

abbrev «毁灭层级» := DestructionLevel

def DestructionLevel.rank : DestructionLevel → Nat
  | .factInstant => 3
  | .factProcess => 2
  | .necessaryPotential => 1
  | .conditionalPotential => 0

def DestructionLevel.StrongerOrEqual (lhs rhs : DestructionLevel) : Prop :=
  rhs.rank ≤ lhs.rank

theorem DestructionLevel.strongerOrEqual_refl (lvl : DestructionLevel) :
    lvl.StrongerOrEqual lvl := by
  simp [DestructionLevel.StrongerOrEqual]

theorem DestructionLevel.strongerOrEqual_trans
    {a b c : DestructionLevel}
    (hab : a.StrongerOrEqual b)
    (hbc : b.StrongerOrEqual c) :
    a.StrongerOrEqual c := by
  unfold DestructionLevel.StrongerOrEqual at hab hbc ⊢
  exact Nat.le_trans hbc hab

theorem DestructionLevel.factInstant_strongerOrEqual_factProcess :
    DestructionLevel.StrongerOrEqual .factInstant .factProcess := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

theorem DestructionLevel.factInstant_strongerOrEqual_necessaryPotential :
    DestructionLevel.StrongerOrEqual .factInstant .necessaryPotential := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

theorem DestructionLevel.factInstant_strongerOrEqual_conditionalPotential :
    DestructionLevel.StrongerOrEqual .factInstant .conditionalPotential := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

theorem DestructionLevel.factProcess_strongerOrEqual_necessaryPotential :
    DestructionLevel.StrongerOrEqual .factProcess .necessaryPotential := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

theorem DestructionLevel.factProcess_strongerOrEqual_conditionalPotential :
    DestructionLevel.StrongerOrEqual .factProcess .conditionalPotential := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

theorem DestructionLevel.necessaryPotential_strongerOrEqual_conditionalPotential :
    DestructionLevel.StrongerOrEqual .necessaryPotential .conditionalPotential := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

theorem DestructionLevel.conditionalPotential_not_strongerOrEqual_factProcess :
    ¬ DestructionLevel.StrongerOrEqual .conditionalPotential .factProcess := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

theorem DestructionLevel.conditionalPotential_not_strongerOrEqual_factInstant :
    ¬ DestructionLevel.StrongerOrEqual .conditionalPotential .factInstant := by
  simp [DestructionLevel.StrongerOrEqual, DestructionLevel.rank]

namespace «毁灭层级»

abbrev «事实瞬时毁灭» : «毁灭层级» := DestructionLevel.factInstant
abbrev «事实过程毁灭» : «毁灭层级» := DestructionLevel.factProcess
abbrev «必然潜能毁灭» : «毁灭层级» := DestructionLevel.necessaryPotential
abbrev «条件潜能毁灭» : «毁灭层级» := DestructionLevel.conditionalPotential
abbrev «强于等于» := DestructionLevel.StrongerOrEqual

end «毁灭层级»

end VerseFramework
