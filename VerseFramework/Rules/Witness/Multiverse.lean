import VerseFramework.Rules.Multiverse
import VerseFramework.Rules.Witness.Monadic

namespace VerseFramework

inductive FamilySupportWitness (ctx : RuleContext) (f : FamilyId) : Prop where
  | multipleIndependent (h : FamilyFactWitness ctx f .textStatesMultipleIndependentWorlds)
  | distinctComplete (h : FamilyFactWitness ctx f .textStatesDistinctCompleteWorlds)

def FamilySupportWitness.proves
    {ctx : RuleContext} {f : FamilyId}
    (w : FamilySupportWitness ctx f) :
    FamilySupport ctx f := by
  cases w with
  | multipleIndependent h => exact Or.inl h.proves
  | distinctComplete h => exact Or.inr h.proves

theorem familySupport_iff_witness (ctx : RuleContext) (f : FamilyId) :
    FamilySupport ctx f ↔ FamilySupportWitness ctx f := by
  constructor
  · intro h
    rcases h with h | h
    · exact .multipleIndependent (.direct h)
    · exact .distinctComplete (.direct h)
  · intro h
    exact h.proves

abbrev «宇宙族文本支持见证» := FamilySupportWitness
abbrev «宇宙族文本支持当且仅当存在见证» := familySupport_iff_witness

inductive CausalIndependenceSupportWitness
    (ctx : RuleContext) (u v : WorldId) : Prop where
  | forward (h : PairFactWitness ctx u v .causallyIndependent)
  | backward (h : PairFactWitness ctx v u .causallyIndependent)

def CausalIndependenceSupportWitness.proves
    {ctx : RuleContext} {u v : WorldId}
    (w : CausalIndependenceSupportWitness ctx u v) :
    ctx.HasPairFact u v .causallyIndependent ∨
      ctx.HasPairFact v u .causallyIndependent := by
  cases w with
  | forward h => exact Or.inl h.proves
  | backward h => exact Or.inr h.proves

structure CausallyIndependentWitness (ctx : RuleContext) (u v : WorldId) : Prop where
  «支持» : CausalIndependenceSupportWitness ctx u v
  «无阻断» : ¬ CausalDependenceBlocker ctx u v

namespace CausallyIndependentWitness

abbrev support {ctx : RuleContext} {u v : WorldId} := @CausallyIndependentWitness.«支持» ctx u v
abbrev noBlock {ctx : RuleContext} {u v : WorldId} := @CausallyIndependentWitness.«无阻断» ctx u v

end CausallyIndependentWitness

def CausallyIndependentWitness.proves
    {ctx : RuleContext} {u v : WorldId}
    (w : CausallyIndependentWitness ctx u v) :
    CausallyIndependent ctx u v :=
  ⟨w.support.proves, w.noBlock⟩

theorem causallyIndependent_iff_witness (ctx : RuleContext) (u v : WorldId) :
    CausallyIndependent ctx u v ↔ CausallyIndependentWitness ctx u v := by
  constructor
  · intro h
    rcases h with ⟨hSupport, hNoBlock⟩
    rcases hSupport with hForward | hBackward
    · exact { «支持» := .forward (.direct hForward), «无阻断» := hNoBlock }
    · exact { «支持» := .backward (.direct hBackward), «无阻断» := hNoBlock }
  · intro h
    exact h.proves

abbrev «因果独立见证» := CausallyIndependentWitness
abbrev «因果独立当且仅当存在见证» := causallyIndependent_iff_witness

inductive BranchIndependenceSupportWitness (ctx : RuleContext) (u v : WorldId) : Prop where
  | forwardCoexist (h : PairFactWitness ctx u v .branchesCoexistAsRealWorlds)
  | backwardCoexist (h : PairFactWitness ctx v u .branchesCoexistAsRealWorlds)
  | forwardNoRecoupling (h : PairFactWitness ctx u v .noBranchRecoupling)
  | backwardNoRecoupling (h : PairFactWitness ctx v u .noBranchRecoupling)

def BranchIndependenceSupportWitness.proves
    {ctx : RuleContext} {u v : WorldId}
    (w : BranchIndependenceSupportWitness ctx u v) :
    BranchIndependenceSupport ctx u v := by
  cases w with
  | forwardCoexist h => exact Or.inl h.proves
  | backwardCoexist h => exact Or.inr (Or.inl h.proves)
  | forwardNoRecoupling h => exact Or.inr (Or.inr (Or.inl h.proves))
  | backwardNoRecoupling h => exact Or.inr (Or.inr (Or.inr h.proves))

theorem branchIndependenceSupport_iff_witness
    (ctx : RuleContext) (u v : WorldId) :
    BranchIndependenceSupport ctx u v ↔
      BranchIndependenceSupportWitness ctx u v := by
  constructor
  · intro h
    rcases h with h | h
    · exact .forwardCoexist (.direct h)
    · rcases h with h | h
      · exact .backwardCoexist (.direct h)
      · rcases h with h | h
        · exact .forwardNoRecoupling (.direct h)
        · exact .backwardNoRecoupling (.direct h)
  · intro h
    exact h.proves

abbrev «分支独立支持见证» := BranchIndependenceSupportWitness
abbrev «分支独立支持当且仅当存在见证» := branchIndependenceSupport_iff_witness

inductive DynamicallyIndependentPairWitness (ctx : RuleContext) (u v : WorldId) : Prop where
  | directForward
      (h : PairFactWitness ctx u v .dynamicallyIndependent)
      (hNoBlock : ¬ PairDynamicsDependenceBlocker ctx u v)
  | directBackward
      (h : PairFactWitness ctx v u .dynamicallyIndependent)
      (hNoBlock : ¬ PairDynamicsDependenceBlocker ctx u v)
  | causalBridge
      (hCausal : CausallyIndependentWitness ctx u v)
      (hNoBlock : ¬ PairDynamicsDependenceBlocker ctx u v)
  | branchingBridge
      (hBranch : BranchIndependenceSupportWitness ctx u v)
      (hNoBlock : ¬ PairDynamicsDependenceBlocker ctx u v)
  | autonomousWorldsBridge
      (hu : AutonomousWorldDynamicsWitness ctx u)
      (hv : AutonomousWorldDynamicsWitness ctx v)
      (hNoBlock : ¬ PairDynamicsDependenceBlocker ctx u v)

def DynamicallyIndependentPairWitness.proves
    {ctx : RuleContext} {u v : WorldId}
    (w : DynamicallyIndependentPairWitness ctx u v) :
    DynamicallyIndependentPair ctx u v := by
  cases w with
  | directForward h hNoBlock => exact ⟨Or.inl h.proves, hNoBlock⟩
  | directBackward h hNoBlock => exact ⟨Or.inr (Or.inl h.proves), hNoBlock⟩
  | causalBridge hCausal hNoBlock =>
      exact ⟨Or.inr (Or.inr (Or.inl hCausal.proves)), hNoBlock⟩
  | branchingBridge hBranch hNoBlock =>
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl hBranch.proves))), hNoBlock⟩
  | autonomousWorldsBridge hu hv hNoBlock =>
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨hu.proves, hv.proves⟩))), hNoBlock⟩

theorem dynamicallyIndependentPair_iff_witness
    (ctx : RuleContext) (u v : WorldId) :
    DynamicallyIndependentPair ctx u v ↔
      DynamicallyIndependentPairWitness ctx u v := by
  constructor
  · intro h
    rcases h with ⟨hSupport, hNoBlock⟩
    rcases hSupport with hForward | hRest
    · exact .directForward (.direct hForward) hNoBlock
    · rcases hRest with hBackward | hRest
      · exact .directBackward (.direct hBackward) hNoBlock
      · rcases hRest with hCausal | hRest
        · exact .causalBridge ((causallyIndependent_iff_witness ctx u v).mp hCausal) hNoBlock
        · rcases hRest with hBranch | hAutonomous
          · exact .branchingBridge
              ((branchIndependenceSupport_iff_witness ctx u v).mp hBranch)
              hNoBlock
          · exact .autonomousWorldsBridge
              ((autonomousWorldDynamics_iff_witness ctx u).mp hAutonomous.1)
              ((autonomousWorldDynamics_iff_witness ctx v).mp hAutonomous.2)
              hNoBlock
  · intro h
    exact h.proves

abbrev «配对动力独立见证» := DynamicallyIndependentPairWitness
abbrev «配对动力独立当且仅当存在见证» := dynamicallyIndependentPair_iff_witness

inductive FamilyHasAtLeastTwoMembersWitness
    (family : UniverseFamily) : Prop where
  | mk
      (left : WorldId)
      (leftMember : family.member left)
      (right : WorldId)
      (rightMember : family.member right)
      (distinct : left ≠ right) :
      FamilyHasAtLeastTwoMembersWitness family

def FamilyHasAtLeastTwoMembersWitness.proves
    {family : UniverseFamily}
    (w : FamilyHasAtLeastTwoMembersWitness family) :
    FamilyHasAtLeastTwoMembers family := by
  cases w with
  | mk left leftMember right rightMember distinct =>
      exact ⟨left, leftMember, right, rightMember, distinct⟩

theorem familyHasAtLeastTwoMembers_iff_witness
    (family : UniverseFamily) :
    FamilyHasAtLeastTwoMembers family ↔
      FamilyHasAtLeastTwoMembersWitness family := by
  constructor
  · intro h
    rcases h with ⟨left, hLeft, right, hRight, hDistinct⟩
    exact .mk left hLeft right hRight hDistinct
  · intro h
    exact h.proves

abbrev «宇宙族至少有两个成员见证» := FamilyHasAtLeastTwoMembersWitness
abbrev «宇宙族至少有两个成员当且仅当存在见证» := familyHasAtLeastTwoMembers_iff_witness

structure FamilyAllMembersArgumentWitness
    (ctx : RuleContext) (family : UniverseFamily) : Prop where
  «成员见证» :
    ∀ u, family.member u → MonadicArgumentWitness ctx .destructionQualified u

namespace FamilyAllMembersArgumentWitness

abbrev memberWitness {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyAllMembersArgumentWitness.«成员见证» ctx family

end FamilyAllMembersArgumentWitness

def FamilyAllMembersArgumentWitness.proves
    {ctx : RuleContext} {family : UniverseFamily}
    (w : FamilyAllMembersArgumentWitness ctx family) :
    FamilyAllMembersSupportArgument ctx family := by
  intro u hu
  exact (w.memberWitness u hu).proves

theorem familyAllMembersSupportArgument_iff_witness
    (ctx : RuleContext) (family : UniverseFamily) :
    FamilyAllMembersSupportArgument ctx family ↔
      FamilyAllMembersArgumentWitness ctx family := by
  constructor
  · intro h
    exact
      { «成员见证» := fun u hu =>
          (supportsMonadicArgument_iff_witness ctx .destructionQualified u).mp (h u hu) }
  · intro h
    exact h.proves

abbrev «全体成员支持破坏合格单体论证见证» := FamilyAllMembersArgumentWitness
abbrev «全体成员支持破坏合格单体论证当且仅当存在见证» :=
  familyAllMembersSupportArgument_iff_witness

structure FamilyAllMembersMonadicWitness
    (ctx : RuleContext) (family : UniverseFamily) : Prop where
  «成员见证» :
    ∀ u, family.member u → MonadicUniverseWitness ctx u

namespace FamilyAllMembersMonadicWitness

abbrev memberWitness {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyAllMembersMonadicWitness.«成员见证» ctx family

end FamilyAllMembersMonadicWitness

def FamilyAllMembersMonadicWitness.proves
    {ctx : RuleContext} {family : UniverseFamily}
    (w : FamilyAllMembersMonadicWitness ctx family) :
    FamilyAllMembersMonadic ctx family := by
  intro u hu
  exact (w.memberWitness u hu).proves

theorem familyAllMembersMonadic_iff_witness
    (ctx : RuleContext) (family : UniverseFamily) :
    FamilyAllMembersMonadic ctx family ↔
      FamilyAllMembersMonadicWitness ctx family := by
  constructor
  · intro h
    exact
      { «成员见证» := fun u hu =>
          (isMonadicUniverse_iff_witness ctx u).mp (h u hu) }
  · intro h
    exact h.proves

abbrev «全体成员是单体宇宙见证» := FamilyAllMembersMonadicWitness
abbrev «全体成员是单体宇宙当且仅当存在见证» := familyAllMembersMonadic_iff_witness

structure FamilyPairwiseIndependenceWitness
    (ctx : RuleContext) (family : UniverseFamily) : Prop where
  «配对见证» :
    ∀ u v, family.member u → family.member v → u ≠ v →
      CausallyIndependentWitness ctx u v ∧
      DynamicallyIndependentPairWitness ctx u v

namespace FamilyPairwiseIndependenceWitness

abbrev pairWitness {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyPairwiseIndependenceWitness.«配对见证» ctx family

end FamilyPairwiseIndependenceWitness

def FamilyPairwiseIndependenceWitness.proves
    {ctx : RuleContext} {family : UniverseFamily}
    (w : FamilyPairwiseIndependenceWitness ctx family) :
    FamilyPairwiseIndependent ctx family := by
  intro u v hu hv hne
  let hPair := w.pairWitness u v hu hv hne
  exact ⟨hPair.1.proves, hPair.2.proves⟩

theorem familyPairwiseIndependent_iff_witness
    (ctx : RuleContext) (family : UniverseFamily) :
    FamilyPairwiseIndependent ctx family ↔
      FamilyPairwiseIndependenceWitness ctx family := by
  constructor
  · intro h
    exact
      { «配对见证» := fun u v hu hv hne =>
          let hPair := h u v hu hv hne
          And.intro
            ((causallyIndependent_iff_witness ctx u v).mp hPair.1)
            ((dynamicallyIndependentPair_iff_witness ctx u v).mp hPair.2) }
  · intro h
    exact h.proves

abbrev «全体成员两两独立见证» := FamilyPairwiseIndependenceWitness
abbrev «全体成员两两独立当且仅当存在见证» := familyPairwiseIndependent_iff_witness

inductive MultiverseArgumentWitness (ctx : RuleContext) (family : UniverseFamily) : Prop where
  | mk
      (familySupport : FamilySupportWitness ctx family.name)
      (noBlock : ¬ FamilyBlocker ctx family.name)
      (left : WorldId)
      (leftMember : family.member left)
      (right : WorldId)
      (rightMember : family.member right)
      (distinct : left ≠ right)
      (leftArgument : MonadicArgumentWitness ctx .destructionQualified left)
      (rightArgument : MonadicArgumentWitness ctx .destructionQualified right)
      (causal : CausallyIndependentWitness ctx left right)
      (dynamics : DynamicallyIndependentPairWitness ctx left right) :
      MultiverseArgumentWitness ctx family

def MultiverseArgumentWitness.proves
    {ctx : RuleContext} {family : UniverseFamily}
    (w : MultiverseArgumentWitness ctx family) :
    SupportsMultiverseArgument ctx family := by
  cases w with
  | mk familySupport noBlock left leftMember right rightMember distinct leftArgument rightArgument causal dynamics =>
      exact ⟨familySupport.proves, noBlock, left, leftMember, right, rightMember,
        distinct, leftArgument.proves, rightArgument.proves, causal.proves, dynamics.proves⟩

theorem supportsMultiverseArgument_iff_witness
    (ctx : RuleContext) (family : UniverseFamily) :
    SupportsMultiverseArgument ctx family ↔
      MultiverseArgumentWitness ctx family := by
  constructor
  · intro h
    rcases h with ⟨hFamily, hNoBlock, left, hLeft, right, hRight, hDistinct,
      hLeftArg, hRightArg, hCausal, hDynamics⟩
    exact .mk
      ((familySupport_iff_witness ctx family.name).mp hFamily)
      hNoBlock
      left
      hLeft
      right
      hRight
      hDistinct
      ((supportsMonadicArgument_iff_witness ctx .destructionQualified left).mp hLeftArg)
      ((supportsMonadicArgument_iff_witness ctx .destructionQualified right).mp hRightArg)
      ((causallyIndependent_iff_witness ctx left right).mp hCausal)
      ((dynamicallyIndependentPair_iff_witness ctx left right).mp hDynamics)
  · intro h
    exact h.proves

abbrev «多宇宙论证见证» := MultiverseArgumentWitness
abbrev «多宇宙论证当且仅当存在见证» := supportsMultiverseArgument_iff_witness

structure FamilyStrictMultiverseArgumentWitness
    (ctx : RuleContext) (family : UniverseFamily) : Prop where
  «宇宙族支持» : FamilySupportWitness ctx family.name
  «无阻断» : ¬ FamilyBlocker ctx family.name
  «至少两员» : FamilyHasAtLeastTwoMembersWitness family
  «全体成员» : FamilyAllMembersArgumentWitness ctx family
  «两两独立» : FamilyPairwiseIndependenceWitness ctx family

namespace FamilyStrictMultiverseArgumentWitness

abbrev familySupport {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseArgumentWitness.«宇宙族支持» ctx family
abbrev noBlock {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseArgumentWitness.«无阻断» ctx family
abbrev atLeastTwo {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseArgumentWitness.«至少两员» ctx family
abbrev allMembers {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseArgumentWitness.«全体成员» ctx family
abbrev pairwise {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseArgumentWitness.«两两独立» ctx family

end FamilyStrictMultiverseArgumentWitness

def FamilyStrictMultiverseArgumentWitness.proves
    {ctx : RuleContext} {family : UniverseFamily}
    (w : FamilyStrictMultiverseArgumentWitness ctx family) :
    SupportsFamilyStrictMultiverseArgument ctx family :=
  ⟨w.familySupport.proves, w.noBlock, w.atLeastTwo.proves, w.allMembers.proves, w.pairwise.proves⟩

theorem supportsFamilyStrictMultiverseArgument_iff_witness
    (ctx : RuleContext) (family : UniverseFamily) :
    SupportsFamilyStrictMultiverseArgument ctx family ↔
      FamilyStrictMultiverseArgumentWitness ctx family := by
  constructor
  · intro h
    exact
      { «宇宙族支持» := (familySupport_iff_witness ctx family.name).mp h.1
        «无阻断» := h.2.1
        «至少两员» := (familyHasAtLeastTwoMembers_iff_witness family).mp h.2.2.1
        «全体成员» :=
          (familyAllMembersSupportArgument_iff_witness ctx family).mp h.2.2.2.1
        «两两独立» :=
          (familyPairwiseIndependent_iff_witness ctx family).mp h.2.2.2.2 }
  · intro h
    exact h.proves

abbrev «严格多宇宙论证见证» := FamilyStrictMultiverseArgumentWitness
abbrev «严格多宇宙论证当且仅当存在见证» :=
  supportsFamilyStrictMultiverseArgument_iff_witness

inductive MultiverseWitness (ctx : RuleContext) (family : UniverseFamily) : Prop where
  | mk
      (familySupport : FamilySupportWitness ctx family.name)
      (noBlock : ¬ FamilyBlocker ctx family.name)
      (left : WorldId)
      (leftMember : family.member left)
      (right : WorldId)
      (rightMember : family.member right)
      (distinct : left ≠ right)
      (leftWorld : MonadicUniverseWitness ctx left)
      (rightWorld : MonadicUniverseWitness ctx right)
      (causal : CausallyIndependentWitness ctx left right)
      (dynamics : DynamicallyIndependentPairWitness ctx left right) :
      MultiverseWitness ctx family

def MultiverseWitness.proves
    {ctx : RuleContext} {family : UniverseFamily}
    (w : MultiverseWitness ctx family) :
    IsMultiverse ctx family := by
  cases w with
  | mk familySupport noBlock left leftMember right rightMember distinct leftWorld rightWorld causal dynamics =>
      exact ⟨familySupport.proves, noBlock, left, leftMember, right, rightMember,
        distinct, leftWorld.proves, rightWorld.proves, causal.proves, dynamics.proves⟩

theorem isMultiverse_iff_witness
    (ctx : RuleContext) (family : UniverseFamily) :
    IsMultiverse ctx family ↔ MultiverseWitness ctx family := by
  constructor
  · intro h
    rcases h with ⟨hFamily, hNoBlock, left, hLeft, right, hRight, hDistinct,
      hLeftWorld, hRightWorld, hCausal, hDynamics⟩
    exact .mk
      ((familySupport_iff_witness ctx family.name).mp hFamily)
      hNoBlock
      left
      hLeft
      right
      hRight
      hDistinct
      ((isMonadicUniverse_iff_witness ctx left).mp hLeftWorld)
      ((isMonadicUniverse_iff_witness ctx right).mp hRightWorld)
      ((causallyIndependent_iff_witness ctx left right).mp hCausal)
      ((dynamicallyIndependentPair_iff_witness ctx left right).mp hDynamics)
  · intro h
    exact h.proves

abbrev «多宇宙见证» := MultiverseWitness
abbrev «多宇宙当且仅当存在见证» := isMultiverse_iff_witness

structure FamilyStrictMultiverseWitness
    (ctx : RuleContext) (family : UniverseFamily) : Prop where
  «宇宙族支持» : FamilySupportWitness ctx family.name
  «无阻断» : ¬ FamilyBlocker ctx family.name
  «至少两员» : FamilyHasAtLeastTwoMembersWitness family
  «全体成员» : FamilyAllMembersMonadicWitness ctx family
  «两两独立» : FamilyPairwiseIndependenceWitness ctx family

namespace FamilyStrictMultiverseWitness

abbrev familySupport {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseWitness.«宇宙族支持» ctx family
abbrev noBlock {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseWitness.«无阻断» ctx family
abbrev atLeastTwo {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseWitness.«至少两员» ctx family
abbrev allMembers {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseWitness.«全体成员» ctx family
abbrev pairwise {ctx : RuleContext} {family : UniverseFamily} :=
  @FamilyStrictMultiverseWitness.«两两独立» ctx family

end FamilyStrictMultiverseWitness

def FamilyStrictMultiverseWitness.proves
    {ctx : RuleContext} {family : UniverseFamily}
    (w : FamilyStrictMultiverseWitness ctx family) :
    IsFamilyStrictMultiverse ctx family :=
  ⟨w.familySupport.proves, w.noBlock, w.atLeastTwo.proves, w.allMembers.proves, w.pairwise.proves⟩

theorem isFamilyStrictMultiverse_iff_witness
    (ctx : RuleContext) (family : UniverseFamily) :
    IsFamilyStrictMultiverse ctx family ↔
      FamilyStrictMultiverseWitness ctx family := by
  constructor
  · intro h
    exact
      { «宇宙族支持» := (familySupport_iff_witness ctx family.name).mp h.1
        «无阻断» := h.2.1
        «至少两员» := (familyHasAtLeastTwoMembers_iff_witness family).mp h.2.2.1
        «全体成员» :=
          (familyAllMembersMonadic_iff_witness ctx family).mp h.2.2.2.1
        «两两独立» :=
          (familyPairwiseIndependent_iff_witness ctx family).mp h.2.2.2.2 }
  · intro h
    exact h.proves

abbrev «严格多宇宙见证» := FamilyStrictMultiverseWitness
abbrev «严格多宇宙当且仅当存在见证» := isFamilyStrictMultiverse_iff_witness

end VerseFramework
