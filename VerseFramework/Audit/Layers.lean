import VerseFramework.Audit.Monadic
import VerseFramework.Audit.Multiverse
import VerseFramework.Audit.Transfinite

namespace VerseFramework

/--
Explicit premise strata used by the checker.

This keeps direct text facts, interpretive bridge rules, and default-assumption
usage separate at the API level, instead of only mentioning them in free-form
audit notes.
-/
inductive PremiseLayer where
  | textFact
  | bridgeRule
  | defaultAssumption
  | structuralWitness
  | blocker
  | missing
  deriving DecidableEq, Repr

abbrev «前提层级» := PremiseLayer

namespace PremiseLayer

def label : PremiseLayer → String
  | .textFact => "text-fact"
  | .bridgeRule => "bridge-rule"
  | .defaultAssumption => "default-assumption"
  | .structuralWitness => "structural-witness"
  | .blocker => "blocker"
  | .missing => "missing"

end PremiseLayer

namespace «前提层级»

abbrev «文本事实» : «前提层级» := PremiseLayer.textFact
abbrev «解释桥接规则» : «前提层级» := PremiseLayer.bridgeRule
abbrev «默认宽限假设» : «前提层级» := PremiseLayer.defaultAssumption
abbrev «结构见证» : «前提层级» := PremiseLayer.structuralWitness
abbrev «阻断» : «前提层级» := PremiseLayer.blocker
abbrev «缺失前提» : «前提层级» := PremiseLayer.missing
abbrev «标签» := PremiseLayer.label

end «前提层级»

def appendLayerIfMissing
    (layers : List PremiseLayer) (layer : PremiseLayer) : List PremiseLayer :=
  if layer ∈ layers then layers else layers ++ [layer]

def mergeLayers
    (base incoming : List PremiseLayer) : List PremiseLayer :=
  incoming.foldl appendLayerIfMissing base

def ConditionSource.usedLayers : ConditionSource → List PremiseLayer
  | .directText => [.textFact]
  | .bridge _ => [.textFact, .bridgeRule]
  | .bridgeWithAssumptions _ _ => [.textFact, .bridgeRule, .defaultAssumption]
  | .structuralWitness => [.structuralWitness]
  | .blocked => [.blocker]
  | .missing => [.missing]

structure LayerSummary where
  «证明状态» : ProofStatus
  «前提层» : List PremiseLayer
  deriving Repr

abbrev «前提来路摘要» := LayerSummary

namespace LayerSummary

abbrev proofStatus := LayerSummary.«证明状态»
abbrev layers := LayerSummary.«前提层»

def HasLayer (summary : LayerSummary) (layer : PremiseLayer) : Prop :=
  layer ∈ summary.«前提层»

def usesTextFacts (summary : LayerSummary) : Prop :=
  summary.HasLayer .textFact

def usesBridgeRules (summary : LayerSummary) : Prop :=
  summary.HasLayer .bridgeRule

def usesAssumptions (summary : LayerSummary) : Prop :=
  summary.HasLayer .defaultAssumption

def hasStructuralWitness (summary : LayerSummary) : Prop :=
  summary.HasLayer .structuralWitness

def isBlocked (summary : LayerSummary) : Prop :=
  summary.HasLayer .blocker

def hasMissingPremise (summary : LayerSummary) : Prop :=
  summary.HasLayer .missing

def renderLines (summary : LayerSummary) : List String :=
  [ s!"ProofStatus: {reprStr summary.proofStatus}"
  , s!"PremiseLayers: {String.intercalate ", " (summary.layers.map PremiseLayer.label)}" ]

end LayerSummary

namespace «层级摘要»

abbrev «证明状态» := LayerSummary.«证明状态»
abbrev «前提层» := LayerSummary.«前提层»
abbrev «具有前提层级» := LayerSummary.HasLayer
abbrev «使用文本事实» := LayerSummary.usesTextFacts
abbrev «使用解释桥接规则» := LayerSummary.usesBridgeRules
abbrev «使用默认宽限假设» := LayerSummary.usesAssumptions
abbrev «具有结构见证» := LayerSummary.hasStructuralWitness
abbrev «被阻断» := LayerSummary.isBlocked
abbrev «存在缺失前提» := LayerSummary.hasMissingPremise
abbrev «渲染行» := LayerSummary.renderLines

end «层级摘要»

def summarizeAudits (audits : List ConditionAudit) : LayerSummary :=
  { «证明状态» := ProofStatus.merge (audits.map ConditionAudit.proofStatus)
    «前提层» :=
      audits.foldl
        (fun acc audit => mergeLayers acc audit.source.usedLayers)
        [] }

def ConditionAudit.layerSummary (audit : ConditionAudit) : LayerSummary :=
  summarizeAudits [audit]

def WorldCoreAudit.layerSummary (audit : WorldCoreAudit) : LayerSummary :=
  summarizeAudits audit.items

def MonadicUniverseAudit.layerSummary (audit : MonadicUniverseAudit) : LayerSummary :=
  summarizeAudits (audit.core.items ++ [audit.independentWhole])

def MonadicArgumentAudit.argumentLayerSummary
    (audit : MonadicArgumentAudit) : LayerSummary :=
  summarizeAudits (audit.core.items ++ [audit.scale])

def MonadicArgumentAudit.strictLayerSummary
    (audit : MonadicArgumentAudit) : LayerSummary :=
  summarizeAudits (audit.core.items ++ [audit.scale, audit.wholeWorld])

def MultiverseAudit.argumentLayerSummary
    (audit : MultiverseAudit) : LayerSummary :=
  summarizeAudits
    [ audit.familySupport
    , audit.leftMember
    , audit.rightMember
    , audit.distinctWorlds
    , audit.leftCore.connected
    , audit.leftCore.spatiotemporal
    , audit.leftCore.dynamics
    , audit.rightCore.connected
    , audit.rightCore.spatiotemporal
    , audit.rightCore.dynamics
    , audit.leftScale
    , audit.rightScale
    , audit.causalIndependence
    , audit.dynamicIndependence ]

def MultiverseAudit.strictLayerSummary
    (audit : MultiverseAudit) : LayerSummary :=
  summarizeAudits
    [ audit.familySupport
    , audit.leftMember
    , audit.rightMember
    , audit.distinctWorlds
    , audit.leftCore.connected
    , audit.leftCore.spatiotemporal
    , audit.leftCore.dynamics
    , audit.rightCore.connected
    , audit.rightCore.spatiotemporal
    , audit.rightCore.dynamics
    , audit.leftScale
    , audit.rightScale
    , audit.causalIndependence
    , audit.dynamicIndependence
    , audit.leftWholeWorld
    , audit.rightWholeWorld ]

def CountableTierAudit.layerSummary (audit : CountableTierAudit) : LayerSummary :=
  summarizeAudits
    [ audit.totalObject
    , audit.blocker
    , audit.memberReality
    , audit.memberIndependence
    , audit.generation
    , audit.closure ]

theorem usesAssumptions_of_bridgeWithAssumptions
    (rule : BridgeRule) (packName : String) :
    LayerSummary.usesAssumptions
      ({ «证明状态» := (.provableUnderAssumptions packName)
         «前提层» := ConditionSource.usedLayers (.bridgeWithAssumptions rule packName) } :
        LayerSummary) := by
  simp [LayerSummary.usesAssumptions, LayerSummary.HasLayer, ConditionSource.usedLayers]

theorem noAssumptions_in_directText_summary (audit : ConditionAudit)
    (h : audit.source = .directText) :
    ¬ LayerSummary.usesAssumptions audit.layerSummary := by
  cases audit with
  | mk label source notes =>
      cases h
      simp [ConditionAudit.layerSummary, summarizeAudits, LayerSummary.usesAssumptions,
        LayerSummary.HasLayer, ConditionSource.usedLayers, mergeLayers,
        appendLayerIfMissing]

theorem noAssumptions_in_directBridge_summary
    (audit : ConditionAudit) (rule : BridgeRule)
    (h : audit.source = .bridge rule) :
    ¬ LayerSummary.usesAssumptions audit.layerSummary := by
  cases audit with
  | mk label source notes =>
      cases h
      simp [ConditionAudit.layerSummary, summarizeAudits, LayerSummary.usesAssumptions,
        LayerSummary.HasLayer, ConditionSource.usedLayers, mergeLayers,
        appendLayerIfMissing]

noncomputable def monadicUniverseLayerSummary
    (ctx : RuleContext) (u : WorldId) : LayerSummary :=
  (monadicUniverseAudit ctx u).layerSummary

noncomputable def monadicArgumentLayerSummary
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : LayerSummary :=
  (monadicArgumentAudit ctx profile u).argumentLayerSummary

noncomputable def monadicArgumentStrictLayerSummary
    (ctx : RuleContext) (profile : ArgumentProfile) (u : WorldId) : LayerSummary :=
  (monadicArgumentAudit ctx profile u).strictLayerSummary

noncomputable def multiverseArgumentLayerSummary
    (ctx : RuleContext) (family : UniverseFamily)
    (left right : WorldId) : LayerSummary :=
  (multiverseAudit ctx family left right).argumentLayerSummary

noncomputable def multiverseStrictLayerSummary
    (ctx : RuleContext) (family : UniverseFamily)
    (left right : WorldId) : LayerSummary :=
  (multiverseAudit ctx family left right).strictLayerSummary

noncomputable def countableTierLayerSummary
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (target : HierarchyTarget) (tier : CountableTier) :
    LayerSummary :=
  (countableTierAudit standard ctx target tier).layerSummary

abbrev «汇总审计层级» := summarizeAudits
abbrev «条件审计层级摘要» := ConditionAudit.layerSummary
abbrev «世界核心层级摘要» := WorldCoreAudit.layerSummary
abbrev «单体宇宙审计层级摘要» := MonadicUniverseAudit.layerSummary
abbrev «单体论证审计层级摘要» := MonadicArgumentAudit.argumentLayerSummary
abbrev «单体论证严格审计层级摘要» := MonadicArgumentAudit.strictLayerSummary
noncomputable abbrev «单体宇宙层级摘要» := monadicUniverseLayerSummary
noncomputable abbrev «单体论证层级摘要» := monadicArgumentLayerSummary
noncomputable abbrev «单体论证严格层级摘要» := monadicArgumentStrictLayerSummary
abbrev «层级摘要» := LayerSummary
noncomputable abbrev «多宇宙论证层级摘要» := multiverseArgumentLayerSummary
noncomputable abbrev «多宇宙严格层级摘要» := multiverseStrictLayerSummary
noncomputable abbrev «超限层级层级摘要» := countableTierLayerSummary

end VerseFramework
