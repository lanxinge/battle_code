import VerseFramework.Rules.Witness.Multiverse
import VerseFramework.Rules.Witness.Destruction
import VerseFramework.Rules.Transfinite

namespace VerseFramework

def «攻击命中目标» (attack : Attack) (target : TargetRef) : Prop :=
  attack.target = target

abbrev AttackTargets := «攻击命中目标»

def «攻击对单体至少达到»
    (ctx : RuleContext) (attack : Attack) (u : WorldId) (lvl : DestructionLevel) : Prop :=
  «攻击命中目标» attack (.world u) ∧
  IsMonadicUniverse ctx u ∧
  AttackAtLeast ctx attack.name lvl

abbrev AttackDestroysWorldAtLeast := «攻击对单体至少达到»

def «攻击对宇宙族至少达到»
    (ctx : RuleContext) (attack : Attack) (family : UniverseFamily)
    (lvl : DestructionLevel) : Prop :=
  «攻击命中目标» attack (.family family.name) ∧
  IsMultiverse ctx family ∧
  AttackAtLeast ctx attack.name lvl

abbrev AttackDestroysFamilyAtLeast := «攻击对宇宙族至少达到»

def «攻击对超限层级至少达到»
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (attack : Attack) (aggregate : AggregateId)
    (tier : CountableTier) (lvl : DestructionLevel) : Prop :=
  «攻击命中目标» attack (.aggregate aggregate) ∧
  SupportsCountableTier standard ctx (.aggregate aggregate) tier ∧
  AttackAtLeast ctx attack.name lvl

abbrev AttackDestroysAggregateTierAtLeast := «攻击对超限层级至少达到»

structure WorldDestructionWitness
    (ctx : RuleContext) (attack : Attack) (u : WorldId) (lvl : DestructionLevel) : Prop where
  «目标» : «攻击命中目标» attack (.world u)
  «世界» : MonadicUniverseWitness ctx u
  «毁灭» : AttackAtLeastWitness ctx attack.name lvl

namespace WorldDestructionWitness

abbrev target {ctx : RuleContext} {attack : Attack} {u : WorldId} {lvl : DestructionLevel} :=
  @WorldDestructionWitness.«目标» ctx attack u lvl
abbrev world {ctx : RuleContext} {attack : Attack} {u : WorldId} {lvl : DestructionLevel} :=
  @WorldDestructionWitness.«世界» ctx attack u lvl
abbrev destruction {ctx : RuleContext} {attack : Attack} {u : WorldId} {lvl : DestructionLevel} :=
  @WorldDestructionWitness.«毁灭» ctx attack u lvl

end WorldDestructionWitness

def WorldDestructionWitness.proves
    {ctx : RuleContext} {attack : Attack} {u : WorldId} {lvl : DestructionLevel}
    (w : WorldDestructionWitness ctx attack u lvl) :
    «攻击对单体至少达到» ctx attack u lvl :=
  ⟨w.target, w.world.proves, w.destruction.proves⟩

theorem «攻击毁灭单体当且仅当存在见证»
    (ctx : RuleContext) (attack : Attack) (u : WorldId) (lvl : DestructionLevel) :
    «攻击对单体至少达到» ctx attack u lvl ↔
      WorldDestructionWitness ctx attack u lvl := by
  constructor
  · intro h
    exact { «目标» := h.1
          , «世界» := (isMonadicUniverse_iff_witness ctx u).mp h.2.1
          , «毁灭» := (attackAtLeast_iff_witness ctx attack.name lvl).mp h.2.2 }
  · intro h
    exact h.proves

abbrev attackDestroysWorldAtLeast_iff_witness
    (ctx : RuleContext) (attack : Attack) (u : WorldId) (lvl : DestructionLevel) :=
  «攻击毁灭单体当且仅当存在见证» ctx attack u lvl

structure FamilyDestructionWitness
    (ctx : RuleContext) (attack : Attack) (family : UniverseFamily) (lvl : DestructionLevel) : Prop where
  «目标» : «攻击命中目标» attack (.family family.name)
  «宇宙族见证» : MultiverseWitness ctx family
  «毁灭» : AttackAtLeastWitness ctx attack.name lvl

namespace FamilyDestructionWitness

abbrev target {ctx : RuleContext} {attack : Attack} {family : UniverseFamily} {lvl : DestructionLevel} :=
  @FamilyDestructionWitness.«目标» ctx attack family lvl
abbrev familyWitness {ctx : RuleContext} {attack : Attack} {family : UniverseFamily} {lvl : DestructionLevel} :=
  @FamilyDestructionWitness.«宇宙族见证» ctx attack family lvl
abbrev destruction {ctx : RuleContext} {attack : Attack} {family : UniverseFamily} {lvl : DestructionLevel} :=
  @FamilyDestructionWitness.«毁灭» ctx attack family lvl

end FamilyDestructionWitness

def FamilyDestructionWitness.proves
    {ctx : RuleContext} {attack : Attack} {family : UniverseFamily} {lvl : DestructionLevel}
    (w : FamilyDestructionWitness ctx attack family lvl) :
    «攻击对宇宙族至少达到» ctx attack family lvl :=
  ⟨w.target, w.familyWitness.proves, w.destruction.proves⟩

theorem «攻击毁灭宇宙族当且仅当存在见证»
    (ctx : RuleContext) (attack : Attack) (family : UniverseFamily) (lvl : DestructionLevel) :
    «攻击对宇宙族至少达到» ctx attack family lvl ↔
      FamilyDestructionWitness ctx attack family lvl := by
  constructor
  · intro h
    exact { «目标» := h.1
          , «宇宙族见证» := (isMultiverse_iff_witness ctx family).mp h.2.1
          , «毁灭» := (attackAtLeast_iff_witness ctx attack.name lvl).mp h.2.2 }
  · intro h
    exact h.proves

abbrev attackDestroysFamilyAtLeast_iff_witness
    (ctx : RuleContext) (attack : Attack) (family : UniverseFamily) (lvl : DestructionLevel) :=
  «攻击毁灭宇宙族当且仅当存在见证» ctx attack family lvl

structure AggregateTierDestructionWitness
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (attack : Attack) (aggregate : AggregateId)
    (tier : CountableTier) (lvl : DestructionLevel) : Prop where
  «目标» : «攻击命中目标» attack (.aggregate aggregate)
  «聚合支持» : SupportsCountableTier standard ctx (.aggregate aggregate) tier
  «毁灭» : AttackAtLeastWitness ctx attack.name lvl

namespace AggregateTierDestructionWitness

abbrev target
    {standard : TransfiniteStandard}
    {ctx : RuleContext} {attack : Attack} {aggregate : AggregateId}
    {tier : CountableTier} {lvl : DestructionLevel} :=
  @AggregateTierDestructionWitness.«目标» standard ctx attack aggregate tier lvl
abbrev aggregateSupport
    {standard : TransfiniteStandard}
    {ctx : RuleContext} {attack : Attack} {aggregate : AggregateId}
    {tier : CountableTier} {lvl : DestructionLevel} :=
  @AggregateTierDestructionWitness.«聚合支持» standard ctx attack aggregate tier lvl
abbrev destruction
    {standard : TransfiniteStandard}
    {ctx : RuleContext} {attack : Attack} {aggregate : AggregateId}
    {tier : CountableTier} {lvl : DestructionLevel} :=
  @AggregateTierDestructionWitness.«毁灭» standard ctx attack aggregate tier lvl

end AggregateTierDestructionWitness

def AggregateTierDestructionWitness.proves
    {standard : TransfiniteStandard}
    {ctx : RuleContext} {attack : Attack} {aggregate : AggregateId}
    {tier : CountableTier} {lvl : DestructionLevel}
    (w : AggregateTierDestructionWitness standard ctx attack aggregate tier lvl) :
    «攻击对超限层级至少达到» standard ctx attack aggregate tier lvl :=
  ⟨w.target, w.aggregateSupport, w.destruction.proves⟩

theorem «攻击毁灭超限层级当且仅当存在见证»
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (attack : Attack) (aggregate : AggregateId)
    (tier : CountableTier) (lvl : DestructionLevel) :
    «攻击对超限层级至少达到» standard ctx attack aggregate tier lvl ↔
      AggregateTierDestructionWitness standard ctx attack aggregate tier lvl := by
  constructor
  · intro h
    exact { «目标» := h.1
          , «聚合支持» := h.2.1
          , «毁灭» := (attackAtLeast_iff_witness ctx attack.name lvl).mp h.2.2 }
  · intro h
    exact h.proves

abbrev attackDestroysAggregateTierAtLeast_iff_witness
    (standard : TransfiniteStandard)
    (ctx : RuleContext) (attack : Attack) (aggregate : AggregateId)
    (tier : CountableTier) (lvl : DestructionLevel) :=
  «攻击毁灭超限层级当且仅当存在见证» standard ctx attack aggregate tier lvl

abbrev «单体破坏见证» := WorldDestructionWitness
abbrev «宇宙族破坏见证» := FamilyDestructionWitness
abbrev «超限层级破坏见证» := AggregateTierDestructionWitness

end VerseFramework
