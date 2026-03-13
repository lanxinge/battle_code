import VerseFramework.Rules.Context

namespace VerseFramework

inductive AssumptionWitness (ctx : RuleContext) : AssumptionFlag → Prop where
  | enabled {flag : AssumptionFlag} (h : ctx.assumptions.allows flag) :
      AssumptionWitness ctx flag

abbrev «假设见证» := AssumptionWitness

def AssumptionWitness.proves
    {ctx : RuleContext} {flag : AssumptionFlag}
    (w : AssumptionWitness ctx flag) :
    ctx.assumptions.allows flag := by
  cases w with
  | enabled h => exact h

inductive WorldFactWitness (ctx : RuleContext) (u : WorldId) : WorldAtom → Prop where
  | direct {atom : WorldAtom} (h : ctx.HasWorldFact u atom) :
      WorldFactWitness ctx u atom

abbrev «世界事实见证» := WorldFactWitness

def WorldFactWitness.proves
    {ctx : RuleContext} {u : WorldId} {atom : WorldAtom}
    (w : WorldFactWitness ctx u atom) :
    ctx.HasWorldFact u atom := by
  cases w with
  | direct h => exact h

inductive PairFactWitness (ctx : RuleContext) (u v : WorldId) : PairAtom → Prop where
  | direct {atom : PairAtom} (h : ctx.HasPairFact u v atom) :
      PairFactWitness ctx u v atom

abbrev «配对事实见证» := PairFactWitness

def PairFactWitness.proves
    {ctx : RuleContext} {u v : WorldId} {atom : PairAtom}
    (w : PairFactWitness ctx u v atom) :
    ctx.HasPairFact u v atom := by
  cases w with
  | direct h => exact h

inductive FamilyFactWitness (ctx : RuleContext) (f : FamilyId) : FamilyAtom → Prop where
  | direct {atom : FamilyAtom} (h : ctx.HasFamilyFact f atom) :
      FamilyFactWitness ctx f atom

abbrev «宇宙族事实见证» := FamilyFactWitness

def FamilyFactWitness.proves
    {ctx : RuleContext} {f : FamilyId} {atom : FamilyAtom}
    (w : FamilyFactWitness ctx f atom) :
    ctx.HasFamilyFact f atom := by
  cases w with
  | direct h => exact h

inductive AttackFactWitness (ctx : RuleContext) (aId : AttackId) : AttackAtom → Prop where
  | direct {atom : AttackAtom} (h : ctx.HasAttackFact aId atom) :
      AttackFactWitness ctx aId atom

abbrev «攻击事实见证» := AttackFactWitness

def AttackFactWitness.proves
    {ctx : RuleContext} {aId : AttackId} {atom : AttackAtom}
    (w : AttackFactWitness ctx aId atom) :
    ctx.HasAttackFact aId atom := by
  cases w with
  | direct h => exact h

abbrev «假设见证得出允许»
    {ctx : RuleContext} {flag : AssumptionFlag} :=
  @AssumptionWitness.proves ctx flag
abbrev «世界事实见证得出事实»
    {ctx : RuleContext} {u : WorldId} {atom : WorldAtom} :=
  @WorldFactWitness.proves ctx u atom
abbrev «配对事实见证得出事实»
    {ctx : RuleContext} {u v : WorldId} {atom : PairAtom} :=
  @PairFactWitness.proves ctx u v atom
abbrev «宇宙族事实见证得出事实»
    {ctx : RuleContext} {f : FamilyId} {atom : FamilyAtom} :=
  @FamilyFactWitness.proves ctx f atom
abbrev «攻击事实见证得出事实»
    {ctx : RuleContext} {aId : AttackId} {atom : AttackAtom} :=
  @AttackFactWitness.proves ctx aId atom

end VerseFramework
