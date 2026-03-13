import VerseFramework.Assumptions.Packs
import VerseFramework.Evidence.Atoms

namespace VerseFramework

structure RuleContext where
  «证据» : TextEvidence
  «假设» : AssumptionPack

abbrev «规则上下文» := RuleContext

namespace RuleContext

abbrev evidence := RuleContext.«证据»
abbrev assumptions := RuleContext.«假设»

end RuleContext

namespace RuleContext

def HasWorldFact (ctx : RuleContext) (u : WorldId) (a : WorldAtom) : Prop :=
  ctx.evidence.worldFact u a

def HasPairFact (ctx : RuleContext) (u v : WorldId) (a : PairAtom) : Prop :=
  ctx.evidence.pairFact u v a

def HasFamilyFact (ctx : RuleContext) (f : FamilyId) (a : FamilyAtom) : Prop :=
  ctx.evidence.familyFact f a

def HasAttackFact (ctx : RuleContext) (aId : AttackId) (a : AttackAtom) : Prop :=
  ctx.evidence.attackFact aId a

def HasAggregateFact (ctx : RuleContext) (aId : AggregateId) (a : AggregateAtom) : Prop :=
  ctx.evidence.aggregateFact aId a

def WorldFactDescriptions (ctx : RuleContext) (u : WorldId) (a : WorldAtom) : List String :=
  ctx.evidence.worldDescriptions u a

def PairFactDescriptions (ctx : RuleContext) (u v : WorldId) (a : PairAtom) : List String :=
  ctx.evidence.pairDescriptions u v a

def FamilyFactDescriptions (ctx : RuleContext) (f : FamilyId) (a : FamilyAtom) : List String :=
  ctx.evidence.familyDescriptions f a

def AttackFactDescriptions (ctx : RuleContext) (aId : AttackId) (a : AttackAtom) : List String :=
  ctx.evidence.attackDescriptions aId a

def AggregateFactDescriptions (ctx : RuleContext) (aId : AggregateId) (a : AggregateAtom) : List String :=
  ctx.evidence.aggregateDescriptions aId a

def WorldAuditTrail (ctx : RuleContext) (u : WorldId) (a : WorldAtom) : List String :=
  let ds := ctx.WorldFactDescriptions u a
  if ds.isEmpty then [ctx.assumptions.worldCoverageNote a] else ds

def PairAuditTrail (ctx : RuleContext) (u v : WorldId) (a : PairAtom) : List String :=
  let ds := ctx.PairFactDescriptions u v a
  if ds.isEmpty then [ctx.assumptions.pairCoverageNote a] else ds

def FamilyAuditTrail (ctx : RuleContext) (f : FamilyId) (a : FamilyAtom) : List String :=
  let ds := ctx.FamilyFactDescriptions f a
  if ds.isEmpty then [ctx.assumptions.familyCoverageNote a] else ds

def AttackAuditTrail (ctx : RuleContext) (aId : AttackId) (a : AttackAtom) : List String :=
  let ds := ctx.AttackFactDescriptions aId a
  if ds.isEmpty then [ctx.assumptions.attackCoverageNote a] else ds

def AggregateAuditTrail (ctx : RuleContext) (aId : AggregateId) (a : AggregateAtom) : List String :=
  let ds := ctx.AggregateFactDescriptions aId a
  if ds.isEmpty then
    [s!"[{ctx.assumptions.name}] no source snippet attached for {reprStr a}; transfinite-tier claims require explicit aggregate evidence."]
  else
    ds

abbrev «具有世界事实» := RuleContext.HasWorldFact
abbrev «具有配对事实» := RuleContext.HasPairFact
abbrev «具有宇宙族事实» := RuleContext.HasFamilyFact
abbrev «具有攻击事实» := RuleContext.HasAttackFact
abbrev «具有聚合事实» := RuleContext.HasAggregateFact
abbrev «世界事实描述» := RuleContext.WorldFactDescriptions
abbrev «配对事实描述» := RuleContext.PairFactDescriptions
abbrev «宇宙族事实描述» := RuleContext.FamilyFactDescriptions
abbrev «攻击事实描述» := RuleContext.AttackFactDescriptions
abbrev «聚合事实描述» := RuleContext.AggregateFactDescriptions
abbrev «世界审计轨迹» := RuleContext.WorldAuditTrail
abbrev «配对审计轨迹» := RuleContext.PairAuditTrail
abbrev «宇宙族审计轨迹» := RuleContext.FamilyAuditTrail
abbrev «攻击审计轨迹» := RuleContext.AttackAuditTrail
abbrev «聚合审计轨迹» := RuleContext.AggregateAuditTrail

end RuleContext

end VerseFramework
