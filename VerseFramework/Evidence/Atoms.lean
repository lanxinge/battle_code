import VerseFramework.Core.Model
import VerseFramework.Core.Transfinite

namespace VerseFramework

structure EvidenceCell where
  «成立» : Prop
  «描述» : List String := []

abbrev «证据单元» := EvidenceCell

namespace EvidenceCell

abbrev holds := EvidenceCell.«成立»
abbrev descriptions := EvidenceCell.«描述»

end EvidenceCell

namespace EvidenceCell

def present (descriptions : List String := []) : EvidenceCell :=
  { «成立» := True, «描述» := descriptions }

def absent : EvidenceCell :=
  { «成立» := False, «描述» := [] }

@[simp] theorem present_holds (descriptions : List String) :
    (EvidenceCell.present descriptions).«成立» := by
  simp [EvidenceCell.present]

@[simp] theorem present_descriptions (descriptions : List String) :
    (EvidenceCell.present descriptions).«描述» = descriptions := by
  simp [EvidenceCell.present]

@[simp] theorem absent_not_holds :
    ¬ EvidenceCell.absent.«成立» := by
  simp [EvidenceCell.absent]

@[simp] theorem absent_descriptions :
    EvidenceCell.absent.«描述» = [] := by
  simp [EvidenceCell.absent]

end EvidenceCell

namespace «证据单元»

abbrev «成立» {cell : EvidenceCell} := cell.«成立»
abbrev «描述» {cell : EvidenceCell} := cell.«描述»
abbrev «存在» := EvidenceCell.present
abbrev «缺失» := EvidenceCell.absent

end «证据单元»

inductive WorldAtom where
  | connectedSpacetimeObject
  | hasSpatialAspect
  | hasTemporalAspect
  | hasSpatialInfinity
  | hasTemporalInfinity
  | hasWorldHistory
  | hasUnifiedDynamics
  | hasAutonomousEvolution
  | hasGlobalEvolution
  | hasCauchyLikeSlices
  | requiresExternalSustenance
  | requiresExternalGovernance
  | presentedAsWholeWorld
  | presentedAsLocalRegion
  | presentedAsPocketSpace
  | presentedAsSubsystem
  | presentedAsFrameworkOnly
  | presentedAsIndexFamily
  | presentedAsPureSpace
  | presentedAsContinuumOnly
  | presentedAsWorldlineStructure
  | presentedAsHilbertSpace
  | presentedAsPhaseSpace
  | presentedAsConfigurationSpace
  | presentedAsBraneFramework
  | explicitlyCalledUniverse
  | presentedInRealistPhysicsSetting
  deriving DecidableEq, Repr

abbrev «世界原子» := WorldAtom

namespace «世界原子»

abbrev «连通时空对象» : «世界原子» := WorldAtom.connectedSpacetimeObject
abbrev «具有空间性» : «世界原子» := WorldAtom.hasSpatialAspect
abbrev «具有时间性» : «世界原子» := WorldAtom.hasTemporalAspect
abbrev «具有空间无限性» : «世界原子» := WorldAtom.hasSpatialInfinity
abbrev «具有时间无限性» : «世界原子» := WorldAtom.hasTemporalInfinity
abbrev «具有世界历史» : «世界原子» := WorldAtom.hasWorldHistory
abbrev «具有统一动力学» : «世界原子» := WorldAtom.hasUnifiedDynamics
abbrev «具有自治演化» : «世界原子» := WorldAtom.hasAutonomousEvolution
abbrev «具有整体演化» : «世界原子» := WorldAtom.hasGlobalEvolution
abbrev «具有类柯西切片» : «世界原子» := WorldAtom.hasCauchyLikeSlices
abbrev «依赖外部维持» : «世界原子» := WorldAtom.requiresExternalSustenance
abbrev «依赖外部支配» : «世界原子» := WorldAtom.requiresExternalGovernance
abbrev «被呈现为完整世界» : «世界原子» := WorldAtom.presentedAsWholeWorld
abbrev «被呈现为局部区域» : «世界原子» := WorldAtom.presentedAsLocalRegion
abbrev «被呈现为口袋空间» : «世界原子» := WorldAtom.presentedAsPocketSpace
abbrev «被呈现为子系统» : «世界原子» := WorldAtom.presentedAsSubsystem
abbrev «被呈现为仅框架» : «世界原子» := WorldAtom.presentedAsFrameworkOnly
abbrev «被呈现为索引族» : «世界原子» := WorldAtom.presentedAsIndexFamily
abbrev «被呈现为纯空间» : «世界原子» := WorldAtom.presentedAsPureSpace
abbrev «被呈现为仅连续统» : «世界原子» := WorldAtom.presentedAsContinuumOnly
abbrev «被呈现为世界线结构» : «世界原子» := WorldAtom.presentedAsWorldlineStructure
abbrev «被呈现为希尔伯特空间» : «世界原子» := WorldAtom.presentedAsHilbertSpace
abbrev «被呈现为相空间» : «世界原子» := WorldAtom.presentedAsPhaseSpace
abbrev «被呈现为配置空间» : «世界原子» := WorldAtom.presentedAsConfigurationSpace
abbrev «被呈现为膜框架» : «世界原子» := WorldAtom.presentedAsBraneFramework
abbrev «被明确称为宇宙» : «世界原子» := WorldAtom.explicitlyCalledUniverse
abbrev «被呈现于写实物理语境» : «世界原子» := WorldAtom.presentedInRealistPhysicsSetting
abbrev «被当作完整世界叙述» : «世界原子» := WorldAtom.presentedAsWholeWorld
abbrev «被当作局部区域叙述» : «世界原子» := WorldAtom.presentedAsLocalRegion
abbrev «被当作口袋空间叙述» : «世界原子» := WorldAtom.presentedAsPocketSpace
abbrev «被当作子系统叙述» : «世界原子» := WorldAtom.presentedAsSubsystem
abbrev «被当作理论框架叙述» : «世界原子» := WorldAtom.presentedAsFrameworkOnly

end «世界原子»

inductive PairAtom where
  | causallyIndependent
  | causallyCoupled
  | dynamicallyIndependent
  | dynamicallyCoupled
  | sharesExternalGovernance
  | requiresJointStateDescription
  | branchesCoexistAsRealWorlds
  | noBranchRecoupling
  deriving DecidableEq, Repr

abbrev «配对原子» := PairAtom

namespace «配对原子»

abbrev «因果独立» : «配对原子» := PairAtom.causallyIndependent
abbrev «因果耦合» : «配对原子» := PairAtom.causallyCoupled
abbrev «动力学独立» : «配对原子» := PairAtom.dynamicallyIndependent
abbrev «动力学耦合» : «配对原子» := PairAtom.dynamicallyCoupled
abbrev «共享外部支配» : «配对原子» := PairAtom.sharesExternalGovernance
abbrev «需要联合状态描述» : «配对原子» := PairAtom.requiresJointStateDescription
abbrev «分支并存为真实世界» : «配对原子» := PairAtom.branchesCoexistAsRealWorlds
abbrev «分支不再回耦» : «配对原子» := PairAtom.noBranchRecoupling

end «配对原子»

inductive FamilyAtom where
  | textStatesMultipleIndependentWorlds
  | textStatesDistinctCompleteWorlds
  | presentedAsFrameworkOnly
  deriving DecidableEq, Repr

abbrev «宇宙族原子» := FamilyAtom

namespace «宇宙族原子»

abbrev «文本陈述多个独立世界» : «宇宙族原子» := FamilyAtom.textStatesMultipleIndependentWorlds
abbrev «文本陈述多个完整世界» : «宇宙族原子» := FamilyAtom.textStatesDistinctCompleteWorlds
abbrev «被呈现为仅框架» : «宇宙族原子» := FamilyAtom.presentedAsFrameworkOnly
abbrev «文本直述复数独立世界» : «宇宙族原子» := FamilyAtom.textStatesMultipleIndependentWorlds
abbrev «文本直述复数完整世界» : «宇宙族原子» := FamilyAtom.textStatesDistinctCompleteWorlds
abbrev «被当作理论框架叙述» : «宇宙族原子» := FamilyAtom.presentedAsFrameworkOnly

end «宇宙族原子»

inductive AttackAtom where
  | factInstantTotalDestruction
  | factProcessTotalDestruction
  | necessaryPotentialTotalDestruction
  | conditionalPotentialTotalDestruction
  deriving DecidableEq, Repr

abbrev «毁灭原子» := AttackAtom
abbrev «攻击原子» := AttackAtom

namespace «毁灭原子»

abbrev «事实瞬时完全毁灭» : «毁灭原子» := AttackAtom.factInstantTotalDestruction
abbrev «事实过程完全毁灭» : «毁灭原子» := AttackAtom.factProcessTotalDestruction
abbrev «必然潜能完全毁灭» : «毁灭原子» := AttackAtom.necessaryPotentialTotalDestruction
abbrev «条件潜能完全毁灭» : «毁灭原子» := AttackAtom.conditionalPotentialTotalDestruction

end «毁灭原子»

namespace «攻击原子»

abbrev «事实瞬时整体毁灭» : «攻击原子» := AttackAtom.factInstantTotalDestruction
abbrev «事实过程整体毁灭» : «攻击原子» := AttackAtom.factProcessTotalDestruction
abbrev «必然潜能整体毁灭» : «攻击原子» := AttackAtom.necessaryPotentialTotalDestruction
abbrev «条件潜能整体毁灭» : «攻击原子» := AttackAtom.conditionalPotentialTotalDestruction

end «攻击原子»

inductive AggregateAtom where
  | presentedAsTotalObject
  | presentedAsFrameworkOnly
  | membersRealizeTierObjectsAt (tier : CountableTier)
  | membersArePairwiseCausallyIndependentAt (tier : CountableTier)
  | membersArePairwiseDynamicallyIndependentAt (tier : CountableTier)
  | membersDoNotRequireExternalSupportAt (tier : CountableTier)
  | generatedHierarchyPresentedAsActualObjects
  | hasExactlyNIndependentMembersAt (tier : CountableTier) (n : Nat)
  | hasCountablyManyIndependentMembersAt (tier : CountableTier)
  | describesOmegaPowerSuccessorRule
  | describesAllFiniteOmegaPowerIterations
  | describesLimitClosureOfPreviousLayers
  | describesDiagonalClosure
  | describesOrdinalRecursiveGenerator
  deriving DecidableEq, Repr

abbrev «聚合原子» := AggregateAtom

namespace «聚合原子»

abbrev «被承认为总体对象» : «聚合原子» := AggregateAtom.presentedAsTotalObject
abbrev «被呈现为仅框架» : «聚合原子» := AggregateAtom.presentedAsFrameworkOnly
def «成员被承认为实际层级对象» (tier : «可数超限层级») : «聚合原子» :=
  AggregateAtom.membersRealizeTierObjectsAt tier
def «成员两两因果独立» (tier : «可数超限层级») : «聚合原子» :=
  AggregateAtom.membersArePairwiseCausallyIndependentAt tier
def «成员两两动力学独立» (tier : «可数超限层级») : «聚合原子» :=
  AggregateAtom.membersArePairwiseDynamicallyIndependentAt tier
def «成员不依赖外部维持» (tier : «可数超限层级») : «聚合原子» :=
  AggregateAtom.membersDoNotRequireExternalSupportAt tier
abbrev «递归生成层级被承认为实际对象» : «聚合原子» :=
  AggregateAtom.generatedHierarchyPresentedAsActualObjects
def «恰有N个独立下层成员» (tier : «可数超限层级») (n : Nat) : «聚合原子» :=
  AggregateAtom.hasExactlyNIndependentMembersAt tier n
def «有可数多个独立下层成员» (tier : «可数超限层级») : «聚合原子» :=
  AggregateAtom.hasCountablyManyIndependentMembersAt tier
abbrev «存在幂后继生成规则» : «聚合原子» := AggregateAtom.describesOmegaPowerSuccessorRule
abbrev «允许全部有限次幂迭代» : «聚合原子» := AggregateAtom.describesAllFiniteOmegaPowerIterations
abbrev «存在前层极限闭包» : «聚合原子» := AggregateAtom.describesLimitClosureOfPreviousLayers
abbrev «存在对角化闭包» : «聚合原子» := AggregateAtom.describesDiagonalClosure
abbrev «存在序数递归生成法» : «聚合原子» := AggregateAtom.describesOrdinalRecursiveGenerator

end «聚合原子»

structure TextEvidence where
  «世界条目» : WorldId → WorldAtom → EvidenceCell
  «配对条目» : WorldId → WorldId → PairAtom → EvidenceCell
  «宇宙族条目» : FamilyId → FamilyAtom → EvidenceCell
  «攻击条目» : AttackId → AttackAtom → EvidenceCell
  «聚合条目» : AggregateId → AggregateAtom → EvidenceCell := fun _ _ => EvidenceCell.absent

abbrev «文本证据» := TextEvidence

namespace TextEvidence

abbrev worldEntry := TextEvidence.«世界条目»
abbrev pairEntry := TextEvidence.«配对条目»
abbrev familyEntry := TextEvidence.«宇宙族条目»
abbrev attackEntry := TextEvidence.«攻击条目»
abbrev aggregateEntry := TextEvidence.«聚合条目»

end TextEvidence

namespace TextEvidence

def worldFact (e : TextEvidence) (u : WorldId) (a : WorldAtom) : Prop :=
  (e.worldEntry u a).holds

def pairFact (e : TextEvidence) (u v : WorldId) (a : PairAtom) : Prop :=
  (e.pairEntry u v a).holds

def familyFact (e : TextEvidence) (f : FamilyId) (a : FamilyAtom) : Prop :=
  (e.familyEntry f a).holds

def attackFact (e : TextEvidence) (aId : AttackId) (a : AttackAtom) : Prop :=
  (e.attackEntry aId a).holds

def aggregateFact (e : TextEvidence) (aId : AggregateId) (a : AggregateAtom) : Prop :=
  (e.aggregateEntry aId a).holds

def worldDescriptions (e : TextEvidence) (u : WorldId) (a : WorldAtom) : List String :=
  (e.worldEntry u a).descriptions

def pairDescriptions (e : TextEvidence) (u v : WorldId) (a : PairAtom) : List String :=
  (e.pairEntry u v a).descriptions

def familyDescriptions (e : TextEvidence) (f : FamilyId) (a : FamilyAtom) : List String :=
  (e.familyEntry f a).descriptions

def attackDescriptions (e : TextEvidence) (aId : AttackId) (a : AttackAtom) : List String :=
  (e.attackEntry aId a).descriptions

def aggregateDescriptions (e : TextEvidence) (aId : AggregateId) (a : AggregateAtom) : List String :=
  (e.aggregateEntry aId a).descriptions

@[simp] theorem worldFact_eq_holds (e : TextEvidence) (u : WorldId) (a : WorldAtom) :
    e.worldFact u a = (e.worldEntry u a).holds := rfl

@[simp] theorem pairFact_eq_holds (e : TextEvidence) (u v : WorldId) (a : PairAtom) :
    e.pairFact u v a = (e.pairEntry u v a).holds := rfl

@[simp] theorem familyFact_eq_holds (e : TextEvidence) (f : FamilyId) (a : FamilyAtom) :
    e.familyFact f a = (e.familyEntry f a).holds := rfl

@[simp] theorem attackFact_eq_holds (e : TextEvidence) (aId : AttackId) (a : AttackAtom) :
    e.attackFact aId a = (e.attackEntry aId a).holds := rfl

@[simp] theorem aggregateFact_eq_holds (e : TextEvidence) (aId : AggregateId) (a : AggregateAtom) :
    e.aggregateFact aId a = (e.aggregateEntry aId a).holds := rfl

end TextEvidence

def TextEvidence.empty : TextEvidence :=
  { «世界条目» := fun _ _ => EvidenceCell.absent
    «配对条目» := fun _ _ _ => EvidenceCell.absent
    «宇宙族条目» := fun _ _ => EvidenceCell.absent
    «攻击条目» := fun _ _ => EvidenceCell.absent
    «聚合条目» := fun _ _ => EvidenceCell.absent }

namespace «文本证据»

abbrev «空» := TextEvidence.empty

end «文本证据»

end VerseFramework
