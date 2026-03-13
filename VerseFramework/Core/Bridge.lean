namespace VerseFramework

inductive BridgeRule where
  | connectedFromCauchyLikeSlices
  | temporalFromWorldHistory
  | temporalFromRealistPhysicsSetting
  | autonomousEvolutionFromUnifiedDynamics
  | autonomousEvolutionFromWorldHistory
  | autonomousEvolutionFromRealistPhysicsSetting
  | unifiedDynamicsFromWorldHistory
  | unifiedDynamicsFromRealistPhysicsSetting
  | wholeWorldFromExplicitUniverseLabel
  | dynamicIndependenceFromCausalIndependence
  | dynamicIndependenceFromAutonomousWorlds
  deriving DecidableEq, Repr

abbrev «桥接规则» := BridgeRule

namespace BridgeRule

def label : BridgeRule → String
  | .connectedFromCauchyLikeSlices => "connected-from-cauchy-like-slices"
  | .temporalFromWorldHistory => "temporal-from-world-history"
  | .temporalFromRealistPhysicsSetting => "temporal-from-realist-physics-setting"
  | .autonomousEvolutionFromUnifiedDynamics => "autonomous-evolution-from-unified-dynamics"
  | .autonomousEvolutionFromWorldHistory => "autonomous-evolution-from-world-history"
  | .autonomousEvolutionFromRealistPhysicsSetting =>
      "autonomous-evolution-from-realist-physics-setting"
  | .unifiedDynamicsFromWorldHistory => "unified-dynamics-from-world-history"
  | .unifiedDynamicsFromRealistPhysicsSetting => "unified-dynamics-from-realist-physics-setting"
  | .wholeWorldFromExplicitUniverseLabel => "whole-world-from-explicit-universe-label"
  | .dynamicIndependenceFromCausalIndependence =>
      "dynamic-independence-from-causal-independence"
  | .dynamicIndependenceFromAutonomousWorlds =>
      "dynamic-independence-from-autonomous-worlds"

end BridgeRule

namespace «桥接规则»

abbrev «由类柯西切片得连通性» : «桥接规则» := BridgeRule.connectedFromCauchyLikeSlices
abbrev «由世界历史得时间性» : «桥接规则» := BridgeRule.temporalFromWorldHistory
abbrev «由写实物理语境得时间性» : «桥接规则» := BridgeRule.temporalFromRealistPhysicsSetting
abbrev «由统一动力学得自治演化» : «桥接规则» := BridgeRule.autonomousEvolutionFromUnifiedDynamics
abbrev «由世界历史得自治演化» : «桥接规则» := BridgeRule.autonomousEvolutionFromWorldHistory
abbrev «由写实物理语境得自治演化» : «桥接规则» := BridgeRule.autonomousEvolutionFromRealistPhysicsSetting
abbrev «由世界历史得统一动力学» : «桥接规则» := BridgeRule.unifiedDynamicsFromWorldHistory
abbrev «由写实物理语境得统一动力学» : «桥接规则» := BridgeRule.unifiedDynamicsFromRealistPhysicsSetting
abbrev «由明确宇宙标签得完整世界性» : «桥接规则» := BridgeRule.wholeWorldFromExplicitUniverseLabel
abbrev «由因果独立得动力独立» : «桥接规则» := BridgeRule.dynamicIndependenceFromCausalIndependence
abbrev «由双侧自治得动力独立» : «桥接规则» := BridgeRule.dynamicIndependenceFromAutonomousWorlds

end «桥接规则»

end VerseFramework
