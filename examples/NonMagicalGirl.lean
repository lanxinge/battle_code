import VerseFramework

namespace VerseFramework.Examples.NonMagicalGirl

open VerseFramework

local notation "连通时空对象" => WorldAtom.connectedSpacetimeObject
local notation "具有空间性" => WorldAtom.hasSpatialAspect
local notation "具有时间性" => WorldAtom.hasTemporalAspect
local notation "具有统一动力学" => WorldAtom.hasUnifiedDynamics
local notation "具有空间无限性" => WorldAtom.hasSpatialInfinity
local notation "具有时间无限性" => WorldAtom.hasTemporalInfinity
local notation "被呈现为完整世界" => WorldAtom.presentedAsWholeWorld
local notation "被呈现为口袋空间" => WorldAtom.presentedAsPocketSpace
local notation "被明确称为宇宙" => WorldAtom.explicitlyCalledUniverse

local notation "因果独立" => PairAtom.causallyIndependent
local notation "动力学独立" => PairAtom.dynamicallyIndependent

local notation "文本陈述多个独立世界" => FamilyAtom.textStatesMultipleIndependentWorlds

local notation "事实瞬时整体毁灭" => AttackAtom.factInstantTotalDestruction
local notation "事实过程整体毁灭" => AttackAtom.factProcessTotalDestruction
local notation "条件潜能整体毁灭" => AttackAtom.conditionalPotentialTotalDestruction

local notation "事实瞬时毁灭" => DestructionLevel.factInstant
local notation "事实过程毁灭" => DestructionLevel.factProcess
local notation "必然潜能毁灭" => DestructionLevel.necessaryPotential
local notation "条件潜能毁灭" => DestructionLevel.conditionalPotential

/--
把《非.魔法少女》的宇宙学判断与破坏层判断合并在同一个示例中。

这个文件同时编码三类结论：
1. 故事主宇宙和子宇宙都可作为单体宇宙候选；
2. 黑洞繁殖叙述支持一个严格的双成员多宇宙见证族；
3. 破坏层面上，陨星崩坠、随手一击、永恒终结分别只达到文本明确支持的层级。

同时保留一个负面门槛：
世界之环虽然很大，但文本把它写成近似结界的口袋空间对象，
所以不能把对它的攻击直接上调成对单体宇宙的毁灭判定。
-/
def «总证据» : «文本证据» where
  «世界条目»
    | "故事宇宙", 连通时空对象 =>
        .present
          [ "“个体的结束与整体无关，作为整体的宇宙将会永存。”"
          , "“这是一个永远膨胀的世界，没有尽头的宇宙，被阉割的宇宙。”"
          ]
    | "故事宇宙", 具有空间性 =>
        .present
          [ "“这是一个永远膨胀的世界，没有尽头的宇宙，被阉割的宇宙。”"
          , "“无数行星就这样在魔法光波中化为齑粉。”"
          ]
    | "故事宇宙", 具有时间性 =>
        .present
          [ "“遗憾的是，宇宙的死亡似乎无法回避。”"
          , "“这是一个永远膨胀的世界，没有尽头的宇宙，被阉割的宇宙。”"
          ]
    | "故事宇宙", 具有统一动力学 =>
        .present
          [ "“孵化者将广义相对论和量子力学相结合，建成了大统一理论，成功解释了支配宇宙的力量——引力、电磁力、强核力、弱核力，以及不断增加的熵。”"
          ]
    | "故事宇宙", 具有空间无限性 =>
        .present
          [ "“没有尽头的宇宙。”" ]
    | "故事宇宙", 具有时间无限性 =>
        .present
          [ "“这是一个永远膨胀的世界。”" ]
    | "故事宇宙", 被呈现为完整世界 =>
        .present
          [ "“个体的结束与整体无关，作为整体的宇宙将会永存。”"
          , "文本在该段把对象直接当作整体宇宙，而不是局部区域、口袋空间或单纯框架。"
          ]
    | "故事宇宙", 被明确称为宇宙 =>
        .present
          [ "“这是一个永远膨胀的世界，没有尽头的宇宙，被阉割的宇宙。”" ]
    | "子宇宙", 连通时空对象 =>
        .present
          [ "“宇宙内部的奇点，正是其独立于自身的另一个宇宙。”"
          , "这里的子宇宙被叙述为独立于母体宇宙的完整宇宙对象。"
          ]
    | "子宇宙", 具有空间性 =>
        .present
          [ "“当一颗恒星爆炸成超新星，最终形成黑洞时，就意味着子宇宙的诞生。”"
          ]
    | "子宇宙", 具有时间性 =>
        .present
          [ "“当一颗恒星爆炸成超新星，最终形成黑洞时，就意味着子宇宙的诞生。”"
          ]
    | "子宇宙", 具有统一动力学 =>
        .present
          [ "“当一颗恒星爆炸成超新星，最终形成黑洞时，就意味着子宇宙的诞生。”"
          , "该段仍处于现实宇宙学叙述里，子宇宙被视为受物理生成规则支配的宇宙对象。"
          ]
    | "子宇宙", 被呈现为完整世界 =>
        .present
          [ "“宇宙内部的奇点，正是其独立于自身的另一个宇宙。”" ]
    | "子宇宙", 被明确称为宇宙 =>
        .present
          [ "“宇宙内部的奇点，正是其独立于自身的另一个宇宙。”"
          , "“当一颗恒星爆炸成超新星，最终形成黑洞时，就意味着子宇宙的诞生。”"
          ]
    | "世界之环", 具有空间性 =>
        .present
          [ "“世界之环的面积远大于银河系所有行星面积的总和。”" ]
    | "世界之环", 被呈现为口袋空间 =>
        .present
          [ "“这里不是正常的时空，和人类时代的魔女结界更加相似。Homo Magica已经借助魔力，建立了一个近乎无边无际的结界。”"
          , "文本把世界之环写成结界式构造世界，而不是自然成立的完整宇宙。"
          ]
    | _, _ => .absent
  «配对条目»
    | "故事宇宙", "子宇宙", 因果独立 =>
        .present
          [ "“宇宙内部的奇点，正是其独立于自身的另一个宇宙。”"
          ]
    | "故事宇宙", "子宇宙", 动力学独立 =>
        .present
          [ "“宇宙内部的奇点，正是其独立于自身的另一个宇宙。”"
          , "该段把子宇宙当作脱离母宇宙局部动力学控制的另一宇宙。"
          ]
    | _, _, _ => .absent
  «宇宙族条目»
    | "黑洞谱系", 文本陈述多个独立世界 =>
        .present
          [ "“宇宙是会繁殖的。”"
          , "“宇宙内部的奇点，正是其独立于自身的另一个宇宙。”"
          , "“通过代代相传，后代的宇宙产生了难以计数的海量黑洞。”"
          ]
    | _, _ => .absent
  «攻击条目»
    | "陨星崩坠", 事实过程整体毁灭 =>
        .present
          [ "“这是毁灭，世界的毁灭，坚实的物理法则被空前的力量彻底颠覆，整个世界都在走向崩溃。”"
          ]
    | "随手一击", 事实瞬时整体毁灭 =>
        .present
          [ "“我的世界被毁灭了。Homo Magica只是轻轻一击，从银河系各处逃散至此的远古人类和智能生物都瞬间死去了。”"
          , "“对于Homo Magica来说，毁灭一个行星就像少女为自己准备早餐一样简单。”"
          ]
    | "永恒终结", 条件潜能整体毁灭 =>
        .present
          [ "“从空间的终结到永恒的终结，她们要确立自己无可动摇的统治。”"
          , "“永恒的终结成为可能。”"
          ]
    | _, _ => .absent

def «规则环境» : «规则上下文» :=
  { «证据» := «总证据»
    «假设» := «保守包» }

def «黑洞谱系» : «宇宙族» :=
  { «名称» := "黑洞谱系"
    «成员» := fun u => u = "故事宇宙" ∨ u = "子宇宙" }

def «随手一击攻击» : «破坏» :=
  { «名称» := "随手一击"
    «目标» := «破坏对象».«世界» "世界之环"
    «描述» := "Homo Magica 对世界之环场景对象施加的随手一击。" }

theorem «陨星崩坠精确达到事实过程毁灭» :
    «精确毁灭层级» «规则环境» "陨星崩坠" 事实过程毁灭 := by
  change («总证据».«攻击条目» "陨星崩坠" 事实过程整体毁灭).«成立»
  simp [«总证据», EvidenceCell.present]

theorem «陨星崩坠至少达到事实过程毁灭» :
    «攻击至少达到» «规则环境» "陨星崩坠" 事实过程毁灭 := by
  exact «精确事态可推出至少同级事态» «陨星崩坠精确达到事实过程毁灭»

theorem «陨星崩坠至少达到必然潜能毁灭» :
    «攻击至少达到» «规则环境» "陨星崩坠" 必然潜能毁灭 := by
  exact «事实过程可推出至少必然潜能» «陨星崩坠精确达到事实过程毁灭»

theorem «陨星崩坠至少达到条件潜能毁灭» :
    «攻击至少达到» «规则环境» "陨星崩坠" 条件潜能毁灭 := by
  exact «事实过程可推出至少条件潜能» «陨星崩坠精确达到事实过程毁灭»

theorem «随手一击精确达到事实瞬时毁灭» :
    «精确毁灭层级» «规则环境» "随手一击" 事实瞬时毁灭 := by
  change («总证据».«攻击条目» "随手一击" 事实瞬时整体毁灭).«成立»
  simp [«总证据», EvidenceCell.present]

theorem «随手一击至少达到事实瞬时毁灭» :
    «攻击至少达到» «规则环境» "随手一击" 事实瞬时毁灭 := by
  exact «精确事态可推出至少同级事态» «随手一击精确达到事实瞬时毁灭»

theorem «随手一击至少达到事实过程毁灭» :
    «攻击至少达到» «规则环境» "随手一击" 事实过程毁灭 := by
  exact «事实瞬时可推出至少事实过程» «随手一击精确达到事实瞬时毁灭»

theorem «随手一击至少达到必然潜能毁灭» :
    «攻击至少达到» «规则环境» "随手一击" 必然潜能毁灭 := by
  exact «事实瞬时可推出至少必然潜能» «随手一击精确达到事实瞬时毁灭»

theorem «随手一击至少达到条件潜能毁灭» :
    «攻击至少达到» «规则环境» "随手一击" 条件潜能毁灭 := by
  exact «事实瞬时可推出至少条件潜能» «随手一击精确达到事实瞬时毁灭»

theorem «永恒终结精确达到条件潜能毁灭» :
    «精确毁灭层级» «规则环境» "永恒终结" 条件潜能毁灭 := by
  change («总证据».«攻击条目» "永恒终结" 条件潜能整体毁灭).«成立»
  simp [«总证据», EvidenceCell.present]

theorem «永恒终结至少达到条件潜能毁灭» :
    «攻击至少达到» «规则环境» "永恒终结" 条件潜能毁灭 := by
  exact «精确事态可推出至少同级事态» «永恒终结精确达到条件潜能毁灭»

theorem «世界之环不是单体宇宙» :
    ¬ «是单体宇宙» «规则环境» "世界之环" := by
  apply «口袋空间不能判为单体»
  change («总证据».«世界条目» "世界之环" 被呈现为口袋空间).«成立»
  simp [«总证据», EvidenceCell.present]

theorem «随手一击不能上调为单体宇宙毁灭» :
    ¬ «攻击对单体至少达到» «规则环境» «随手一击攻击» "世界之环" 事实瞬时毁灭 := by
  intro h
  exact «世界之环不是单体宇宙» h.2.1

def «陨星崩坠事实过程见证» :
    «攻击至少达到见证» «规则环境» "陨星崩坠" 事实过程毁灭 :=
  («攻击至少达到当且仅当存在见证» «规则环境» "陨星崩坠" 事实过程毁灭).mp
    «陨星崩坠至少达到事实过程毁灭»

def «随手一击事实瞬时见证» :
    «攻击至少达到见证» «规则环境» "随手一击" 事实瞬时毁灭 :=
  («攻击至少达到当且仅当存在见证» «规则环境» "随手一击" 事实瞬时毁灭).mp
    «随手一击至少达到事实瞬时毁灭»

def «永恒终结条件潜能见证» :
    «攻击至少达到见证» «规则环境» "永恒终结" 条件潜能毁灭 :=
  («攻击至少达到当且仅当存在见证» «规则环境» "永恒终结" 条件潜能毁灭).mp
    «永恒终结至少达到条件潜能毁灭»

noncomputable def «单体宇宙审核»
    (ctx : «规则上下文») (u : «世界标识») : «单体宇宙审计» :=
  monadicUniverseAudit ctx u

noncomputable def «多宇宙审核»
    (ctx : «规则上下文») (family : «宇宙族»)
    (left right : «世界标识») : «多宇宙审计» :=
  multiverseAudit ctx family left right

def «单体宇宙审计转文本» (audit : «单体宇宙审计») : List String :=
  MonadicUniverseAudit.renderLines audit

def «多宇宙审计转文本» (audit : «多宇宙审计») : List String :=
  MultiverseAudit.renderLines audit

/--
以下是这个合并示例的主要产出：
1. 故事宇宙与子宇宙的单体宇宙审计和判定；
2. 黑洞谱系的严格多宇宙审计、层级摘要与判定；
3. 世界之环的失败案例；
4. 破坏层定理与对应见证。
-/
noncomputable def «故事宇宙审计结果» : «单体宇宙审计» :=
  «单体宇宙审核» «规则环境» "故事宇宙"

noncomputable def «子宇宙审计结果» : «单体宇宙审计» :=
  «单体宇宙审核» «规则环境» "子宇宙"

noncomputable def «世界之环审计结果» : «单体宇宙审计» :=
  «单体宇宙审核» «规则环境» "世界之环"

noncomputable def «黑洞谱系审计结果» : «多宇宙审计» :=
  «多宇宙审核» «规则环境» «黑洞谱系» "故事宇宙" "子宇宙"

noncomputable def «故事宇宙层级摘要结果» : «层级摘要» :=
  «单体宇宙层级摘要» «规则环境» "故事宇宙"

noncomputable def «黑洞谱系严格层级摘要结果» : «层级摘要» :=
  «多宇宙严格层级摘要» «规则环境» «黑洞谱系» "故事宇宙" "子宇宙"

noncomputable def «世界之环层级摘要结果» : «层级摘要» :=
  «单体宇宙层级摘要» «规则环境» "世界之环"

noncomputable def «故事宇宙判定结果» : «判定» «断言» :=
  «单体宇宙判定» «规则环境» "故事宇宙"

noncomputable def «故事宇宙论证判定结果» : «判定» «断言» :=
  «单体论证判定» «规则环境» «论证档位».«破坏合格» "故事宇宙"

noncomputable def «子宇宙判定结果» : «判定» «断言» :=
  «单体宇宙判定» «规则环境» "子宇宙"

noncomputable def «黑洞谱系判定结果» : «判定» «断言» :=
  «多宇宙判定» «规则环境» «黑洞谱系» "故事宇宙" "子宇宙"

noncomputable def «世界之环判定结果» : «判定» «断言» :=
  «单体宇宙判定» «规则环境» "世界之环"

noncomputable def «黑洞谱系论证判定结果» : «判定» «断言» :=
  «多宇宙论证判定» «规则环境» «黑洞谱系» "故事宇宙" "子宇宙"

noncomputable def «故事宇宙审计文本» : List String :=
  «单体宇宙审计转文本» «故事宇宙审计结果»

noncomputable def «子宇宙审计文本» : List String :=
  «单体宇宙审计转文本» «子宇宙审计结果»

noncomputable def «黑洞谱系审计文本» : List String :=
  «多宇宙审计转文本» «黑洞谱系审计结果»

noncomputable def «世界之环审计文本» : List String :=
  «单体宇宙审计转文本» «世界之环审计结果»

end VerseFramework.Examples.NonMagicalGirl
