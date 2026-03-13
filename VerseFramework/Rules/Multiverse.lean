import VerseFramework.Rules.Monadic

namespace VerseFramework

def FamilySupport (ctx : RuleContext) (f : FamilyId) : Prop :=
  ctx.HasFamilyFact f .textStatesMultipleIndependentWorlds ∨
  ctx.HasFamilyFact f .textStatesDistinctCompleteWorlds

def FamilyBlocker (ctx : RuleContext) (f : FamilyId) : Prop :=
  ctx.HasFamilyFact f .presentedAsFrameworkOnly

def CausalDependenceBlocker (ctx : RuleContext) (u v : WorldId) : Prop :=
  ctx.HasPairFact u v .causallyCoupled ∨
  ctx.HasPairFact v u .causallyCoupled

def CausallyIndependent (ctx : RuleContext) (u v : WorldId) : Prop :=
  (ctx.HasPairFact u v .causallyIndependent ∨
    ctx.HasPairFact v u .causallyIndependent) ∧
  ¬ CausalDependenceBlocker ctx u v

def BranchIndependenceSupport (ctx : RuleContext) (u v : WorldId) : Prop :=
  ctx.HasPairFact u v .branchesCoexistAsRealWorlds ∨
  ctx.HasPairFact v u .branchesCoexistAsRealWorlds ∨
  ctx.HasPairFact u v .noBranchRecoupling ∨
  ctx.HasPairFact v u .noBranchRecoupling

def PairDynamicsDependenceBlocker (ctx : RuleContext) (u v : WorldId) : Prop :=
  ctx.HasPairFact u v .dynamicallyCoupled ∨
  ctx.HasPairFact v u .dynamicallyCoupled ∨
  ctx.HasPairFact u v .sharesExternalGovernance ∨
  ctx.HasPairFact v u .sharesExternalGovernance ∨
  ctx.HasPairFact u v .requiresJointStateDescription ∨
  ctx.HasPairFact v u .requiresJointStateDescription ∨
  CausalDependenceBlocker ctx u v

def DynamicallyIndependentPair (ctx : RuleContext) (u v : WorldId) : Prop :=
  (ctx.HasPairFact u v .dynamicallyIndependent ∨
    ctx.HasPairFact v u .dynamicallyIndependent ∨
    CausallyIndependent ctx u v ∨
    BranchIndependenceSupport ctx u v ∨
    (AutonomousWorldDynamics ctx u ∧ AutonomousWorldDynamics ctx v)) ∧
  ¬ PairDynamicsDependenceBlocker ctx u v

def IndependentWorldPairCandidate (ctx : RuleContext) (u v : WorldId) : Prop :=
  u ≠ v ∧
  CausallyIndependent ctx u v ∧
  DynamicallyIndependentPair ctx u v

def FamilyHasAtLeastTwoMembers (family : UniverseFamily) : Prop :=
  ∃ u, family.member u ∧ ∃ v, family.member v ∧ u ≠ v

def FamilyAllMembersSupportArgument
    (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  ∀ u, family.member u → SupportsMonadicArgument ctx .destructionQualified u

def FamilyAllMembersMonadic
    (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  ∀ u, family.member u → IsMonadicUniverse ctx u

def FamilyPairwiseIndependent
    (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  ∀ u v, family.member u → family.member v → u ≠ v →
    CausallyIndependent ctx u v ∧
    DynamicallyIndependentPair ctx u v

def MultiverseCandidate (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  FamilySupport ctx family.name ∧
  ∃ u, family.member u ∧ ∃ v, family.member v ∧
    IndependentWorldPairCandidate ctx u v

def SupportsMultiverseArgument (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  FamilySupport ctx family.name ∧
  ¬ FamilyBlocker ctx family.name ∧
  ∃ u, family.member u ∧ ∃ v, family.member v ∧
    u ≠ v ∧
    SupportsMonadicArgument ctx .destructionQualified u ∧
    SupportsMonadicArgument ctx .destructionQualified v ∧
    CausallyIndependent ctx u v ∧
    DynamicallyIndependentPair ctx u v

def IsMultiverse (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  FamilySupport ctx family.name ∧
  ¬ FamilyBlocker ctx family.name ∧
  ∃ u, family.member u ∧ ∃ v, family.member v ∧
    u ≠ v ∧
    IsMonadicUniverse ctx u ∧
    IsMonadicUniverse ctx v ∧
    CausallyIndependent ctx u v ∧
    DynamicallyIndependentPair ctx u v

def SupportsFamilyStrictMultiverseArgument
    (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  FamilySupport ctx family.name ∧
  ¬ FamilyBlocker ctx family.name ∧
  FamilyHasAtLeastTwoMembers family ∧
  FamilyAllMembersSupportArgument ctx family ∧
  FamilyPairwiseIndependent ctx family

def IsFamilyStrictMultiverse
    (ctx : RuleContext) (family : UniverseFamily) : Prop :=
  FamilySupport ctx family.name ∧
  ¬ FamilyBlocker ctx family.name ∧
  FamilyHasAtLeastTwoMembers family ∧
  FamilyAllMembersMonadic ctx family ∧
  FamilyPairwiseIndependent ctx family

theorem multiverseCandidate_of_isMultiverse
    {ctx : RuleContext} {family : UniverseFamily}
    (h : IsMultiverse ctx family) :
    MultiverseCandidate ctx family := by
  rcases h with ⟨hFamily, _, u, hu, v, hv, hne, _, _, hCausal, hDynamic⟩
  exact ⟨hFamily, u, hu, v, hv, ⟨hne, hCausal, hDynamic⟩⟩

theorem familyHasAtLeastTwoMembers_of_isMultiverse
    {ctx : RuleContext} {family : UniverseFamily}
    (h : IsMultiverse ctx family) :
    FamilyHasAtLeastTwoMembers family := by
  rcases h with ⟨_, _, u, hu, v, hv, hne, _, _, _, _⟩
  exact ⟨u, hu, v, hv, hne⟩

theorem familyHasAtLeastTwoMembers_of_isFamilyStrictMultiverse
    {ctx : RuleContext} {family : UniverseFamily}
    (h : IsFamilyStrictMultiverse ctx family) :
    FamilyHasAtLeastTwoMembers family := by
  exact h.2.2.1

theorem familyAllMembersMonadic_of_isFamilyStrictMultiverse
    {ctx : RuleContext} {family : UniverseFamily}
    (h : IsFamilyStrictMultiverse ctx family) :
    FamilyAllMembersMonadic ctx family := by
  exact h.2.2.2.1

theorem familyPairwiseIndependent_of_isFamilyStrictMultiverse
    {ctx : RuleContext} {family : UniverseFamily}
    (h : IsFamilyStrictMultiverse ctx family) :
    FamilyPairwiseIndependent ctx family := by
  exact h.2.2.2.2

theorem familyAllMembersSupportArgument_of_supportsFamilyStrictMultiverseArgument
    {ctx : RuleContext} {family : UniverseFamily}
    (h : SupportsFamilyStrictMultiverseArgument ctx family) :
    FamilyAllMembersSupportArgument ctx family := by
  exact h.2.2.2.1

theorem familyPairwiseIndependent_of_supportsFamilyStrictMultiverseArgument
    {ctx : RuleContext} {family : UniverseFamily}
    (h : SupportsFamilyStrictMultiverseArgument ctx family) :
    FamilyPairwiseIndependent ctx family := by
  exact h.2.2.2.2

theorem multiverse_requires_two_monadic_worlds
    {ctx : RuleContext} {family : UniverseFamily}
    (h : IsMultiverse ctx family) :
    ∃ u, family.member u ∧ ∃ v, family.member v ∧
      u ≠ v ∧
      IsMonadicUniverse ctx u ∧
      IsMonadicUniverse ctx v ∧
      CausallyIndependent ctx u v ∧
      DynamicallyIndependentPair ctx u v := by
  exact h.2.2

theorem supportsMultiverseArgument_requires_dynamic_independence
    {ctx : RuleContext} {family : UniverseFamily}
    (h : SupportsMultiverseArgument ctx family) :
    ∃ u, family.member u ∧ ∃ v, family.member v ∧
      DynamicallyIndependentPair ctx u v := by
  rcases h with ⟨_, _, u, hu, v, hv, _, _, _, _, hDynamic⟩
  exact ⟨u, hu, v, hv, hDynamic⟩

theorem supportsMultiverseArgument_requires_causal_independence
    {ctx : RuleContext} {family : UniverseFamily}
    (h : SupportsMultiverseArgument ctx family) :
    ∃ u, family.member u ∧ ∃ v, family.member v ∧
      CausallyIndependent ctx u v := by
  rcases h with ⟨_, _, u, hu, v, hv, _, _, _, hCausal, _⟩
  exact ⟨u, hu, v, hv, hCausal⟩

theorem supportsMultiverseArgument_of_supportsFamilyStrictMultiverseArgument
    {ctx : RuleContext} {family : UniverseFamily}
    (h : SupportsFamilyStrictMultiverseArgument ctx family) :
    SupportsMultiverseArgument ctx family := by
  rcases h with ⟨hFamily, hNoBlock, hTwo, hAll, hPairwise⟩
  rcases hTwo with ⟨u, hu, v, hv, hne⟩
  have hLeft := hAll u hu
  have hRight := hAll v hv
  have hPair := hPairwise u v hu hv hne
  exact ⟨hFamily, hNoBlock, u, hu, v, hv, hne, hLeft, hRight, hPair.1, hPair.2⟩

theorem isMultiverse_of_isFamilyStrictMultiverse
    {ctx : RuleContext} {family : UniverseFamily}
    (h : IsFamilyStrictMultiverse ctx family) :
    IsMultiverse ctx family := by
  rcases h with ⟨hFamily, hNoBlock, hTwo, hAll, hPairwise⟩
  rcases hTwo with ⟨u, hu, v, hv, hne⟩
  have hLeft := hAll u hu
  have hRight := hAll v hv
  have hPair := hPairwise u v hu hv hne
  exact ⟨hFamily, hNoBlock, u, hu, v, hv, hne, hLeft, hRight, hPair.1, hPair.2⟩

theorem not_isMultiverse_of_familyFrameworkOnly
    {ctx : RuleContext} {family : UniverseFamily}
    (hFramework : FamilyBlocker ctx family.name) :
    ¬ IsMultiverse ctx family := by
  intro h
  exact h.2.1 hFramework

theorem not_supportsFamilyStrictMultiverseArgument_of_familyFrameworkOnly
    {ctx : RuleContext} {family : UniverseFamily}
    (hFramework : FamilyBlocker ctx family.name) :
    ¬ SupportsFamilyStrictMultiverseArgument ctx family := by
  intro h
  exact h.2.1 hFramework

theorem not_isFamilyStrictMultiverse_of_familyFrameworkOnly
    {ctx : RuleContext} {family : UniverseFamily}
    (hFramework : FamilyBlocker ctx family.name) :
    ¬ IsFamilyStrictMultiverse ctx family := by
  intro h
  exact h.2.1 hFramework

theorem not_supportsFamilyStrictMultiverseArgument_of_member_lacks_argument
    {ctx : RuleContext} {family : UniverseFamily} {u : WorldId}
    (hu : family.member u)
    (hNot : ¬ SupportsMonadicArgument ctx .destructionQualified u) :
    ¬ SupportsFamilyStrictMultiverseArgument ctx family := by
  intro h
  exact hNot (h.2.2.2.1 u hu)

theorem not_isFamilyStrictMultiverse_of_member_not_monadic
    {ctx : RuleContext} {family : UniverseFamily} {u : WorldId}
    (hu : family.member u)
    (hNot : ¬ IsMonadicUniverse ctx u) :
    ¬ IsFamilyStrictMultiverse ctx family := by
  intro h
  exact hNot (h.2.2.2.1 u hu)

theorem not_supportsFamilyStrictMultiverseArgument_of_nonindependent_pair
    {ctx : RuleContext} {family : UniverseFamily} {u v : WorldId}
    (hu : family.member u)
    (hv : family.member v)
    (hne : u ≠ v)
    (hNot :
      ¬ (CausallyIndependent ctx u v ∧ DynamicallyIndependentPair ctx u v)) :
    ¬ SupportsFamilyStrictMultiverseArgument ctx family := by
  intro h
  exact hNot (h.2.2.2.2 u v hu hv hne)

theorem not_isFamilyStrictMultiverse_of_nonindependent_pair
    {ctx : RuleContext} {family : UniverseFamily} {u v : WorldId}
    (hu : family.member u)
    (hv : family.member v)
    (hne : u ≠ v)
    (hNot :
      ¬ (CausallyIndependent ctx u v ∧ DynamicallyIndependentPair ctx u v)) :
    ¬ IsFamilyStrictMultiverse ctx family := by
  intro h
  exact hNot (h.2.2.2.2 u v hu hv hne)

theorem not_causallyIndependent_of_causalDependenceBlocker
    {ctx : RuleContext} {u v : WorldId}
    (hBlocked : CausalDependenceBlocker ctx u v) :
    ¬ CausallyIndependent ctx u v := by
  intro hCausal
  exact hCausal.2 hBlocked

theorem not_dynamicallyIndependentPair_of_pairDynamicsDependenceBlocker
    {ctx : RuleContext} {u v : WorldId}
    (hBlocked : PairDynamicsDependenceBlocker ctx u v) :
    ¬ DynamicallyIndependentPair ctx u v := by
  intro hDynamic
  exact hDynamic.2 hBlocked

theorem dynamicallyIndependentPair_of_causalIndependence
    {ctx : RuleContext} {u v : WorldId}
    (hCausal : CausallyIndependent ctx u v)
    (hNoBlock : ¬ PairDynamicsDependenceBlocker ctx u v) :
    DynamicallyIndependentPair ctx u v := by
  exact ⟨Or.inr (Or.inr (Or.inl hCausal)), hNoBlock⟩

theorem dynamicallyIndependentPair_of_autonomous_worlds
    {ctx : RuleContext} {u v : WorldId}
    (hu : AutonomousWorldDynamics ctx u)
    (hv : AutonomousWorldDynamics ctx v)
    (hNoBlock : ¬ PairDynamicsDependenceBlocker ctx u v) :
    DynamicallyIndependentPair ctx u v := by
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨hu, hv⟩))), hNoBlock⟩

abbrev «宇宙族文本支持» := FamilySupport
abbrev «宇宙族框架阻断» := FamilyBlocker
abbrev «因果依赖阻断» := CausalDependenceBlocker
abbrev «因果独立» := CausallyIndependent
abbrev «分支独立支持» := BranchIndependenceSupport
abbrev «配对动力依赖阻断» := PairDynamicsDependenceBlocker
abbrev «配对动力独立» := DynamicallyIndependentPair
abbrev «独立世界对候选» := IndependentWorldPairCandidate
abbrev «宇宙族至少有两个成员» := FamilyHasAtLeastTwoMembers
abbrev «全体成员支持破坏合格单体论证» := FamilyAllMembersSupportArgument
abbrev «全体成员是单体宇宙» := FamilyAllMembersMonadic
abbrev «全体成员两两独立» := FamilyPairwiseIndependent
abbrev «多宇宙候选» := MultiverseCandidate
abbrev «支持多宇宙论证» := SupportsMultiverseArgument
abbrev «是多宇宙» := IsMultiverse
abbrev «支持家族级严格多宇宙论证» := SupportsFamilyStrictMultiverseArgument
abbrev «是家族级严格多宇宙» := IsFamilyStrictMultiverse

abbrev «是多宇宙可推出多宇宙候选»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @multiverseCandidate_of_isMultiverse ctx family
abbrev «是多宇宙则至少有两个成员»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @familyHasAtLeastTwoMembers_of_isMultiverse ctx family
abbrev «是家族级严格多宇宙则至少有两个成员»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @familyHasAtLeastTwoMembers_of_isFamilyStrictMultiverse ctx family
abbrev «是家族级严格多宇宙则全体成员是单体宇宙»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @familyAllMembersMonadic_of_isFamilyStrictMultiverse ctx family
abbrev «是家族级严格多宇宙则全体成员两两独立»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @familyPairwiseIndependent_of_isFamilyStrictMultiverse ctx family
abbrev «支持家族级严格多宇宙论证则全体成员支持破坏合格单体论证»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @familyAllMembersSupportArgument_of_supportsFamilyStrictMultiverseArgument ctx family
abbrev «支持家族级严格多宇宙论证则全体成员两两独立»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @familyPairwiseIndependent_of_supportsFamilyStrictMultiverseArgument ctx family
abbrev «多宇宙至少要求两个单体成员»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @multiverse_requires_two_monadic_worlds ctx family
abbrev «多宇宙论证至少要求动力独立»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @supportsMultiverseArgument_requires_dynamic_independence ctx family
abbrev «多宇宙论证至少要求因果独立»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @supportsMultiverseArgument_requires_causal_independence ctx family
abbrev «严格多宇宙论证可推出多宇宙论证»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @supportsMultiverseArgument_of_supportsFamilyStrictMultiverseArgument ctx family
abbrev «是家族级严格多宇宙可推出是多宇宙»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @isMultiverse_of_isFamilyStrictMultiverse ctx family
abbrev «宇宙族仅为框架则不能是多宇宙»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @not_isMultiverse_of_familyFrameworkOnly ctx family
abbrev «宇宙族仅为框架则不能支持家族级严格多宇宙论证»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @not_supportsFamilyStrictMultiverseArgument_of_familyFrameworkOnly ctx family
abbrev «宇宙族仅为框架则不能是家族级严格多宇宙»
    {ctx : RuleContext} {family : UniverseFamily} :=
  @not_isFamilyStrictMultiverse_of_familyFrameworkOnly ctx family
abbrev «家族成员缺少破坏合格单体论证则不能支持家族级严格多宇宙论证»
    {ctx : RuleContext} {family : UniverseFamily} {u : WorldId} :=
  @not_supportsFamilyStrictMultiverseArgument_of_member_lacks_argument ctx family u
abbrev «家族成员不是单体宇宙则不能是家族级严格多宇宙»
    {ctx : RuleContext} {family : UniverseFamily} {u : WorldId} :=
  @not_isFamilyStrictMultiverse_of_member_not_monadic ctx family u
abbrev «成员对不独立则不能支持家族级严格多宇宙论证»
    {ctx : RuleContext} {family : UniverseFamily} {u v : WorldId} :=
  @not_supportsFamilyStrictMultiverseArgument_of_nonindependent_pair ctx family u v
abbrev «成员对不独立则不能是家族级严格多宇宙»
    {ctx : RuleContext} {family : UniverseFamily} {u v : WorldId} :=
  @not_isFamilyStrictMultiverse_of_nonindependent_pair ctx family u v
abbrev «因果阻断则不成立因果独立»
    {ctx : RuleContext} {u v : WorldId} :=
  @not_causallyIndependent_of_causalDependenceBlocker ctx u v
abbrev «动力阻断则不成立动力独立»
    {ctx : RuleContext} {u v : WorldId} :=
  @not_dynamicallyIndependentPair_of_pairDynamicsDependenceBlocker ctx u v
abbrev «因果独立且无动力阻断可推出动力独立»
    {ctx : RuleContext} {u v : WorldId} :=
  @dynamicallyIndependentPair_of_causalIndependence ctx u v
abbrev «双方自主演化且无动力阻断可推出动力独立»
    {ctx : RuleContext} {u v : WorldId} :=
  @dynamicallyIndependentPair_of_autonomous_worlds ctx u v

end VerseFramework
