import VerseFramework.Core.Argument
import VerseFramework.Core.Destruction
import VerseFramework.Core.Model
import VerseFramework.Core.Transfinite

namespace VerseFramework

inductive Claim where
  | monadicUniverse (world : WorldId)
  | monadicArgument (world : WorldId) (profile : ArgumentProfile)
  | multiverse (family : FamilyId)
  | multiverseArgument (family : FamilyId)
  | countableOrdinalTier
      (standard : TransfiniteStandard) (target : HierarchyTarget) (tier : CountableTier)
  | destructionAtLeast (attack : AttackId) (level : DestructionLevel)
  | targetedDestructionAtLeast
      (attack : AttackId) (target : TargetRef) (level : DestructionLevel)
  deriving DecidableEq, Repr

abbrev «断言» := Claim

namespace «断言»

def «单体宇宙» (world : WorldId) : «断言» := Claim.monadicUniverse world
def «单体论证» (world : WorldId) (profile : ArgumentProfile) : «断言» :=
  Claim.monadicArgument world profile
def «多宇宙» (family : FamilyId) : «断言» := Claim.multiverse family
def «多宇宙论证» (family : FamilyId) : «断言» := Claim.multiverseArgument family
def «可数序层级» (standard : TransfiniteStandard) (target : HierarchyTarget) (tier : CountableTier) :
    «断言» :=
  Claim.countableOrdinalTier standard target tier
def «至少达到某毁灭层级» (attack : AttackId) (level : DestructionLevel) : «断言» :=
  Claim.destructionAtLeast attack level
def «定向攻击至少达到某毁灭层级»
    (attack : AttackId) (target : TargetRef) (level : DestructionLevel) :
    «断言» :=
  Claim.targetedDestructionAtLeast attack target level

end «断言»

end VerseFramework
