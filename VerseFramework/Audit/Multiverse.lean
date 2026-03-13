import VerseFramework.Audit.Monadic
import VerseFramework.Rules.Multiverse

namespace VerseFramework

structure MultiverseAudit where
  «宇宙族» : FamilyId
  «左世界» : WorldId
  «右世界» : WorldId
  «宇宙族支持» : ConditionAudit
  «左成员» : ConditionAudit
  «右成员» : ConditionAudit
  «不同世界» : ConditionAudit
  «左核心» : WorldCoreAudit
  «右核心» : WorldCoreAudit
  «左尺度» : ConditionAudit
  «右尺度» : ConditionAudit
  «因果独立» : ConditionAudit
  «动力独立» : ConditionAudit
  «左整体世界» : ConditionAudit
  «右整体世界» : ConditionAudit
  deriving Repr

namespace MultiverseAudit

abbrev family := MultiverseAudit.«宇宙族»
abbrev leftWorld := MultiverseAudit.«左世界»
abbrev rightWorld := MultiverseAudit.«右世界»
abbrev familySupport := MultiverseAudit.«宇宙族支持»
abbrev leftMember := MultiverseAudit.«左成员»
abbrev rightMember := MultiverseAudit.«右成员»
abbrev distinctWorlds := MultiverseAudit.«不同世界»
abbrev leftCore := MultiverseAudit.«左核心»
abbrev rightCore := MultiverseAudit.«右核心»
abbrev leftScale := MultiverseAudit.«左尺度»
abbrev rightScale := MultiverseAudit.«右尺度»
abbrev causalIndependence := MultiverseAudit.«因果独立»
abbrev dynamicIndependence := MultiverseAudit.«动力独立»
abbrev leftWholeWorld := MultiverseAudit.«左整体世界»
abbrev rightWholeWorld := MultiverseAudit.«右整体世界»

def argumentStatuses (audit : MultiverseAudit) : List ProofStatus :=
  [ audit.familySupport.proofStatus
  , audit.leftMember.proofStatus
  , audit.rightMember.proofStatus
  , audit.distinctWorlds.proofStatus
  , audit.leftCore.proofStatus
  , audit.rightCore.proofStatus
  , audit.leftScale.proofStatus
  , audit.rightScale.proofStatus
  , audit.causalIndependence.proofStatus
  , audit.dynamicIndependence.proofStatus ]

def strictStatuses (audit : MultiverseAudit) : List ProofStatus :=
  audit.argumentStatuses ++
  [audit.leftWholeWorld.proofStatus, audit.rightWholeWorld.proofStatus]

def argumentProofStatus (audit : MultiverseAudit) : ProofStatus :=
  ProofStatus.merge audit.argumentStatuses

def strictProofStatus (audit : MultiverseAudit) : ProofStatus :=
  ProofStatus.merge audit.strictStatuses

def argumentVerdict (audit : MultiverseAudit) : Verdict Claim :=
  { «断言» := .multiverseArgument audit.family
    «状态» := audit.argumentProofStatus }

def strictVerdict (audit : MultiverseAudit) : Verdict Claim :=
  { «断言» := .multiverse audit.family
    «状态» := audit.strictProofStatus }

def renderLines (audit : MultiverseAudit) : List String :=
  [ s!"Claim: multiverse argument ({audit.family})"
  , s!"ArgumentStatus: {reprStr audit.argumentProofStatus}"
  , s!"StrictStatus: {reprStr audit.strictProofStatus}"
  , "Whole-world remains advisory for the argument-layer status, but required for the strict status." ] ++
  audit.familySupport.renderLines ++
  audit.leftMember.renderLines ++
  audit.rightMember.renderLines ++
  audit.distinctWorlds.renderLines ++
  audit.leftCore.connected.renderLines ++
  audit.leftCore.spatiotemporal.renderLines ++
  audit.leftCore.dynamics.renderLines ++
  audit.rightCore.connected.renderLines ++
  audit.rightCore.spatiotemporal.renderLines ++
  audit.rightCore.dynamics.renderLines ++
  audit.leftScale.renderLines ++
  audit.rightScale.renderLines ++
  audit.causalIndependence.renderLines ++
  audit.dynamicIndependence.renderLines ++
  audit.leftWholeWorld.renderLines ++
  audit.rightWholeWorld.renderLines

end MultiverseAudit

namespace «多宇宙审计»

abbrev «宇宙族» := MultiverseAudit.«宇宙族»
abbrev «左世界» := MultiverseAudit.«左世界»
abbrev «右世界» := MultiverseAudit.«右世界»
abbrev «宇宙族支持» := MultiverseAudit.«宇宙族支持»
abbrev «左成员» := MultiverseAudit.«左成员»
abbrev «右成员» := MultiverseAudit.«右成员»
abbrev «不同世界» := MultiverseAudit.«不同世界»
abbrev «左核心» := MultiverseAudit.«左核心»
abbrev «右核心» := MultiverseAudit.«右核心»
abbrev «左尺度» := MultiverseAudit.«左尺度»
abbrev «右尺度» := MultiverseAudit.«右尺度»
abbrev «因果独立» := MultiverseAudit.«因果独立»
abbrev «动力独立» := MultiverseAudit.«动力独立»
abbrev «左整体世界» := MultiverseAudit.«左整体世界»
abbrev «右整体世界» := MultiverseAudit.«右整体世界»
abbrev «论证状态组» := MultiverseAudit.argumentStatuses
abbrev «严格状态组» := MultiverseAudit.strictStatuses
abbrev «论证证明状态» := MultiverseAudit.argumentProofStatus
abbrev «严格证明状态» := MultiverseAudit.strictProofStatus
abbrev «论证判定» := MultiverseAudit.argumentVerdict
abbrev «严格判定» := MultiverseAudit.strictVerdict
abbrev «渲染行» := MultiverseAudit.renderLines

end «多宇宙审计»

namespace RuleContext

noncomputable def familyFrameworkNotes (ctx : RuleContext) (f : FamilyId) : List String := by
  classical
  if h : ctx.HasFamilyFact f .presentedAsFrameworkOnly then
    exact
      "Blocked by family-level framework presentation." ::
        ctx.FamilyAuditTrail f .presentedAsFrameworkOnly
  else
    exact []

noncomputable def causalDependenceNotes (ctx : RuleContext) (u v : WorldId) : List String := by
  classical
  let forwardNotes :=
    if h : ctx.HasPairFact u v .causallyCoupled then
      "Blocked by explicit causal coupling between the witness worlds." ::
        ctx.PairAuditTrail u v .causallyCoupled
    else []
  let backwardNotes :=
    if h : ctx.HasPairFact v u .causallyCoupled then
      "Blocked by explicit causal coupling between the witness worlds." ::
        ctx.PairAuditTrail v u .causallyCoupled
    else []
  exact forwardNotes ++ backwardNotes

noncomputable def pairDynamicsDependenceNotes (ctx : RuleContext) (u v : WorldId) : List String := by
  classical
  let dynamicCouplingForward :=
    if h : ctx.HasPairFact u v .dynamicallyCoupled then
      "Blocked by explicit dynamic coupling between the witness worlds." ::
        ctx.PairAuditTrail u v .dynamicallyCoupled
    else []
  let dynamicCouplingBackward :=
    if h : ctx.HasPairFact v u .dynamicallyCoupled then
      "Blocked by explicit dynamic coupling between the witness worlds." ::
        ctx.PairAuditTrail v u .dynamicallyCoupled
    else []
  let governanceForward :=
    if h : ctx.HasPairFact u v .sharesExternalGovernance then
      "Blocked by shared external governance over both witness worlds." ::
        ctx.PairAuditTrail u v .sharesExternalGovernance
    else []
  let governanceBackward :=
    if h : ctx.HasPairFact v u .sharesExternalGovernance then
      "Blocked by shared external governance over both witness worlds." ::
        ctx.PairAuditTrail v u .sharesExternalGovernance
    else []
  let jointStateForward :=
    if h : ctx.HasPairFact u v .requiresJointStateDescription then
      "Blocked because the witness worlds require one joint state description for their evolution." ::
        ctx.PairAuditTrail u v .requiresJointStateDescription
    else []
  let jointStateBackward :=
    if h : ctx.HasPairFact v u .requiresJointStateDescription then
      "Blocked because the witness worlds require one joint state description for their evolution." ::
        ctx.PairAuditTrail v u .requiresJointStateDescription
    else []
  exact dynamicCouplingForward ++ dynamicCouplingBackward ++ governanceForward ++
    governanceBackward ++ jointStateForward ++ jointStateBackward ++
    ctx.causalDependenceNotes u v

end RuleContext

noncomputable def familySupportAudit
    (ctx : RuleContext) (family : UniverseFamily) : ConditionAudit := by
  classical
  if hBlocked : FamilyBlocker ctx family.name then
    exact
      { «标签» := "FamilySupport"
        «来源» := .blocked
        «注记» := ctx.familyFrameworkNotes family.name }
  else if hComplete : ctx.HasFamilyFact family.name .textStatesDistinctCompleteWorlds then
    exact
      { «标签» := "FamilySupport"
        «来源» := .directText
        «注记» := ctx.FamilyAuditTrail family.name .textStatesDistinctCompleteWorlds }
  else if hIndependent : ctx.HasFamilyFact family.name .textStatesMultipleIndependentWorlds then
    exact
      { «标签» := "FamilySupport"
        «来源» := .directText
        «注记» := ctx.FamilyAuditTrail family.name .textStatesMultipleIndependentWorlds }
  else
    exact
      { «标签» := "FamilySupport"
        «来源» := .missing
        «注记» := [ "Need an explicit family-level statement that multiple distinct or independent worlds are present." ] }

noncomputable def familyMembershipAudit
    (family : UniverseFamily) (u : WorldId) : ConditionAudit := by
  classical
  if hMember : family.member u then
    exact
      { «标签» := s!"Member({u})"
        «来源» := .structuralWitness
        «注记» := [s!"{u} is included by the formal family predicate {family.name}."] }
  else
    exact
      { «标签» := s!"Member({u})"
        «来源» := .missing
        «注记» := [s!"{u} is not included by the formal family predicate {family.name}."] }

def distinctWorldsAudit (u v : WorldId) : ConditionAudit :=
  if _hDistinct : u ≠ v then
    { «标签» := "DistinctWorlds"
      «来源» := .structuralWitness
      «注记» := [s!"Witness worlds {u} and {v} are distinct."] }
  else
    { «标签» := "DistinctWorlds"
      «来源» := .blocked
      «注记» := [ "A multiverse witness pair cannot use the same world twice." ] }

noncomputable def causalIndependenceAudit
    (ctx : RuleContext) (u v : WorldId) : ConditionAudit := by
  classical
  if hBlocked : CausalDependenceBlocker ctx u v then
    exact
      { «标签» := "CausalIndependence"
        «来源» := .blocked
        «注记» := ctx.causalDependenceNotes u v }
  else if hForward : ctx.HasPairFact u v .causallyIndependent then
    exact
      { «标签» := "CausalIndependence"
        «来源» := .directText
        «注记» := ctx.PairAuditTrail u v .causallyIndependent }
  else if hBackward : ctx.HasPairFact v u .causallyIndependent then
    exact
      { «标签» := "CausalIndependence"
        «来源» := .directText
        «注记» := ctx.PairAuditTrail v u .causallyIndependent }
  else
    exact
      { «标签» := "CausalIndependence"
        «来源» := .missing
        «注记» := [ "Need pair-level evidence that the witness worlds are causally independent." ] }

noncomputable def dynamicIndependenceAudit
    (ctx : RuleContext) (u v : WorldId) : ConditionAudit := by
  classical
  if hBlocked : PairDynamicsDependenceBlocker ctx u v then
    exact
      { «标签» := "DynamicIndependence"
        «来源» := .blocked
        «注记» := ctx.pairDynamicsDependenceNotes u v }
  else if hForward : ctx.HasPairFact u v .dynamicallyIndependent then
    exact
      { «标签» := "DynamicIndependence"
        «来源» := .directText
        «注记» := ctx.PairAuditTrail u v .dynamicallyIndependent }
  else if hBackward : ctx.HasPairFact v u .dynamicallyIndependent then
    exact
      { «标签» := "DynamicIndependence"
        «来源» := .directText
        «注记» := ctx.PairAuditTrail v u .dynamicallyIndependent }
  else if hCausal : CausallyIndependent ctx u v then
    exact
      { «标签» := "DynamicIndependence"
        «来源» := .bridge .dynamicIndependenceFromCausalIndependence
        «注记» :=
          [ "Bridge: causal independence counts as one form of dynamic independence." ]
          ++ (causalIndependenceAudit ctx u v).renderLines }
  else if hBranch : BranchIndependenceSupport ctx u v then
    exact
      { «标签» := "DynamicIndependence"
        «来源» := .directText
        «注记» :=
          [ "Direct branching support: the witness worlds are treated as coexisting or non-recoupling branches." ]
          ++
          (if h : ctx.HasPairFact u v .branchesCoexistAsRealWorlds then
            ctx.PairAuditTrail u v .branchesCoexistAsRealWorlds
          else []) ++
          (if h : ctx.HasPairFact v u .branchesCoexistAsRealWorlds then
            ctx.PairAuditTrail v u .branchesCoexistAsRealWorlds
          else []) ++
          (if h : ctx.HasPairFact u v .noBranchRecoupling then
            ctx.PairAuditTrail u v .noBranchRecoupling
          else []) ++
          (if h : ctx.HasPairFact v u .noBranchRecoupling then
            ctx.PairAuditTrail v u .noBranchRecoupling
          else []) }
  else if hAutonomous : AutonomousWorldDynamics ctx u ∧ AutonomousWorldDynamics ctx v then
    let leftAudit := autonomousEvolutionAudit ctx u
    let rightAudit := autonomousEvolutionAudit ctx v
    let mergedStatus := ProofStatus.merge [leftAudit.proofStatus, rightAudit.proofStatus]
    match mergedStatus with
    | .provableUnderAssumptions packName =>
        exact
          { «标签» := "DynamicIndependence"
            «来源» := .bridgeWithAssumptions
              .dynamicIndependenceFromAutonomousWorlds
              packName
            «注记» :=
              [ "Bridge: each witness world has autonomous evolution under the active assumption pack." ]
              ++ leftAudit.renderLines ++
              rightAudit.renderLines }
    | _ =>
        exact
          { «标签» := "DynamicIndependence"
            «来源» := .bridge .dynamicIndependenceFromAutonomousWorlds
            «注记» :=
              [ "Bridge: each witness world has autonomous evolution, so neither requires the other for continued evolution." ]
              ++ leftAudit.renderLines ++
              rightAudit.renderLines }
  else
    exact
      { «标签» := "DynamicIndependence"
        «来源» := .missing
        «注记» :=
          [ "Need either explicit pair-level dynamic independence, causal independence, branching autonomy, or autonomous world evolution on both sides." ] }

noncomputable def multiverseAudit
    (ctx : RuleContext) (family : UniverseFamily) (left right : WorldId) : MultiverseAudit :=
  { «宇宙族» := family.name
    «左世界» := left
    «右世界» := right
    «宇宙族支持» := familySupportAudit ctx family
    «左成员» := familyMembershipAudit family left
    «右成员» := familyMembershipAudit family right
    «不同世界» := distinctWorldsAudit left right
    «左核心» := worldCoreAudit ctx left
    «右核心» := worldCoreAudit ctx right
    «左尺度» := argumentProfileAudit ctx .destructionQualified left
    «右尺度» := argumentProfileAudit ctx .destructionQualified right
    «因果独立» := causalIndependenceAudit ctx left right
    «动力独立» := dynamicIndependenceAudit ctx left right
    «左整体世界» := independentWholeAudit ctx left
    «右整体世界» := independentWholeAudit ctx right }

noncomputable def multiverseArgumentVerdict
    (ctx : RuleContext) (family : UniverseFamily) (left right : WorldId) : Verdict Claim :=
  (multiverseAudit ctx family left right).argumentVerdict

noncomputable def multiverseStrictVerdict
    (ctx : RuleContext) (family : UniverseFamily) (left right : WorldId) : Verdict Claim :=
  (multiverseAudit ctx family left right).strictVerdict

abbrev «多宇宙审计» := MultiverseAudit
noncomputable abbrev «宇宙族支持审计» := familySupportAudit
noncomputable abbrev «宇宙族成员审计» := familyMembershipAudit
abbrev «不同世界审计» := distinctWorldsAudit
noncomputable abbrev «因果独立审计» := causalIndependenceAudit
noncomputable abbrev «动力独立审计» := dynamicIndependenceAudit
noncomputable abbrev «多宇宙论证判定» := multiverseArgumentVerdict
noncomputable abbrev «多宇宙判定» := multiverseStrictVerdict

end VerseFramework
