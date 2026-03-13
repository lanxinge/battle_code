import VerseFramework.Core.Bridge
import VerseFramework.Core.Status

namespace VerseFramework

inductive ConditionSource where
  | directText
  | bridge (rule : BridgeRule)
  | bridgeWithAssumptions (rule : BridgeRule) (packName : String)
  | structuralWitness
  | blocked
  | missing
  deriving DecidableEq, Repr

abbrev «条件来源» := ConditionSource

namespace «条件来源»

abbrev «直接文本» := ConditionSource.directText
abbrev «桥接» := ConditionSource.bridge
abbrev «带假设桥接» := ConditionSource.bridgeWithAssumptions
abbrev «结构见证» := ConditionSource.structuralWitness
abbrev «阻断» := ConditionSource.blocked
abbrev «缺失» := ConditionSource.missing

end «条件来源»

structure ConditionAudit where
  «标签» : String
  «来源» : ConditionSource
  «注记» : List String := []
  deriving Repr

abbrev «条件审计» := ConditionAudit

namespace ConditionAudit

abbrev label := ConditionAudit.«标签»
abbrev source := ConditionAudit.«来源»
abbrev notes := ConditionAudit.«注记»

def sourceLabel : ConditionSource → String
  | .directText => "direct-text"
  | .bridge rule => s!"bridge({rule.label})"
  | .bridgeWithAssumptions rule packName =>
      s!"bridge({rule.label}) via assumptions({packName})"
  | .structuralWitness => "structural-witness"
  | .blocked => "blocked"
  | .missing => "missing"

def supported (audit : ConditionAudit) : Bool :=
  match audit.source with
  | .directText => true
  | .bridge _ => true
  | .bridgeWithAssumptions _ _ => true
  | .structuralWitness => true
  | .blocked => false
  | .missing => false

def usesAssumptions (audit : ConditionAudit) : Bool :=
  match audit.source with
  | .bridgeWithAssumptions _ _ => true
  | _ => false

def isBlocked (audit : ConditionAudit) : Bool :=
  match audit.source with
  | .blocked => true
  | _ => false

def proofStatus (audit : ConditionAudit) : ProofStatus :=
  match audit.source with
  | .directText => .proved
  | .bridge _ => .proved
  | .bridgeWithAssumptions _ packName => .provableUnderAssumptions packName
  | .structuralWitness => .proved
  | .blocked => .refuted
  | .missing => .underdetermined

def renderLines (audit : ConditionAudit) : List String :=
  let header := s!"[{sourceLabel audit.source}] {audit.label}"
  header :: audit.notes.map (fun note => s!"  - {note}")

end ConditionAudit

namespace «条件审计»

abbrev «标签» := ConditionAudit.«标签»
abbrev «来源» := ConditionAudit.«来源»
abbrev «注记» := ConditionAudit.«注记»
abbrev «来源标签» := ConditionAudit.sourceLabel
abbrev «被支持» := ConditionAudit.supported
abbrev «使用假设» := ConditionAudit.usesAssumptions
abbrev «被阻断» := ConditionAudit.isBlocked
abbrev «证明状态» := ConditionAudit.proofStatus
abbrev «渲染行» := ConditionAudit.renderLines

end «条件审计»

namespace ProofStatus

def merge (statuses : List ProofStatus) : ProofStatus :=
  if statuses.any (· == .refuted) then
    .refuted
  else if statuses.any (· == .underdetermined) then
    .underdetermined
  else match statuses.findSome? (fun status =>
      match status with
      | .provableUnderAssumptions packName => some packName
      | _ => none) with
    | some packName => .provableUnderAssumptions packName
    | none => .proved

abbrev «合并» := ProofStatus.merge

end ProofStatus

end VerseFramework
