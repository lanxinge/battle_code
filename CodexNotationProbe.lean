import VerseFramework

open VerseFramework

notation:max "连通时空对象甲" => VerseFramework.WorldAtom.connectedSpacetimeObject
notation:max "因果独立甲" => VerseFramework.PairAtom.causallyIndependent
notation:max "多个独立世界甲" => VerseFramework.FamilyAtom.textStatesMultipleIndependentWorlds

def «测» : «文本证据» where
  «世界条目»
    | "甲", 连通时空对象甲 => .present ["a"]
    | _, _ => .absent
  «配对条目»
    | "甲", "乙", 因果独立甲 => .present ["b"]
    | _, _, _ => .absent
  «宇宙族条目»
    | "丙", 多个独立世界甲 => .present ["c"]
    | _, _ => .absent
  «攻击条目» := fun _ _ => .absent
