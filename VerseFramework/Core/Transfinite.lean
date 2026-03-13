import VerseFramework.Core.Model

namespace VerseFramework

inductive TransfiniteStandard where
  | strict
  | lenient
  deriving DecidableEq, Repr

abbrev «超限标准» := TransfiniteStandard

namespace TransfiniteStandard

def label : TransfiniteStandard → String
  | .strict => "strict"
  | .lenient => "lenient"

end TransfiniteStandard

inductive HierarchyTarget where
  | world (world : WorldId)
  | aggregate (aggregate : AggregateId)
  deriving DecidableEq, Repr

abbrev «层级目标» := HierarchyTarget

inductive CountableTier where
  | omega
  | omegaMulNat (n : Nat)
  | omegaPowNat (n : Nat)
  | omegaPowOmega
  | fixedPoint (label : String)
  deriving DecidableEq, Repr

abbrev «可数超限层级» := CountableTier

namespace CountableTier

def label : CountableTier → String
  | .omega => "omega"
  | .omegaMulNat n => s!"omega*{n}"
  | .omegaPowNat n => s!"omega^{n}"
  | .omegaPowOmega => "omega^omega"
  | .fixedPoint label => label

def isValid : CountableTier → Prop
  | .omega => True
  | .omegaMulNat n => 2 ≤ n
  | .omegaPowNat n => 2 ≤ n
  | .omegaPowOmega => True
  | .fixedPoint _ => True

def predecessor? : CountableTier → Option CountableTier
  | .omegaPowNat 2 => some .omega
  | .omegaPowNat (n + 3) => some (.omegaPowNat (n + 2))
  | _ => none

theorem omegaMulNat_valid {n : Nat} (h : 2 ≤ n) :
    CountableTier.isValid (.omegaMulNat n) := h

theorem omegaPowNat_valid {n : Nat} (h : 2 ≤ n) :
    CountableTier.isValid (.omegaPowNat n) := h

end CountableTier

namespace «超限标准»

abbrev «严格» : «超限标准» := TransfiniteStandard.strict
abbrev «宽松» : «超限标准» := TransfiniteStandard.lenient

end «超限标准»

namespace «层级目标»

abbrev «世界» := HierarchyTarget.world
abbrev «聚合» := HierarchyTarget.aggregate

end «层级目标»

namespace «可数超限层级»

abbrev «单体» : «可数超限层级» := CountableTier.omega
def «多元» (n : Nat) : «可数超限层级» := CountableTier.omegaMulNat n
def «盒子» (n : Nat) : «可数超限层级» := CountableTier.omegaPowNat n
abbrev «无限盒子» : «可数超限层级» := CountableTier.omegaPowOmega
def «指数塔不动点» (label : String) : «可数超限层级» := CountableTier.fixedPoint label

end «可数超限层级»

end VerseFramework
