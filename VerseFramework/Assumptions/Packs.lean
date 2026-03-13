import VerseFramework.Evidence.Atoms

namespace VerseFramework

inductive AssumptionFlag where
  | temporalFromWorldHistory
  | unifiedDynamicsFromHistory
  | autonomousEvolutionFromHistory
  | wholeWorldFromExplicitUniverseLabel
  | connectedFromCauchyLikeSlices
  | weakRealistCosmology
  deriving DecidableEq, Repr

abbrev «假设标记» := AssumptionFlag

structure AssumptionPack where
  «名称» : String
  «允许» : AssumptionFlag → Prop
  «世界覆盖说明» : WorldAtom → String
  «配对覆盖说明» : PairAtom → String
  «宇宙族覆盖说明» : FamilyAtom → String
  «攻击覆盖说明» : AttackAtom → String

abbrev «假设包» := AssumptionPack

namespace AssumptionPack

abbrev name := AssumptionPack.«名称»
abbrev allows := AssumptionPack.«允许»
abbrev worldCoverageNote := AssumptionPack.«世界覆盖说明»
abbrev pairCoverageNote := AssumptionPack.«配对覆盖说明»
abbrev familyCoverageNote := AssumptionPack.«宇宙族覆盖说明»
abbrev attackCoverageNote := AssumptionPack.«攻击覆盖说明»

end AssumptionPack

def AssumptionPack.Extends (lhs rhs : AssumptionPack) : Prop :=
  ∀ flag, rhs.«允许» flag → lhs.«允许» flag

def ConservativePack : AssumptionPack :=
  { «名称» := "ConservativePack"
    «允许» := fun _ => False
    «世界覆盖说明» := fun atom =>
      s!"[ConservativePack] no source snippet attached for {reprStr atom}; no charity beyond explicit assertion."
    «配对覆盖说明» := fun atom =>
      s!"[ConservativePack] no source snippet attached for {reprStr atom}; no charity beyond explicit assertion."
    «宇宙族覆盖说明» := fun atom =>
      s!"[ConservativePack] no source snippet attached for {reprStr atom}; no charity beyond explicit assertion."
    «攻击覆盖说明» := fun atom =>
      s!"[ConservativePack] no source snippet attached for {reprStr atom}; no charity beyond explicit assertion." }

def MildCharityPack : AssumptionPack :=
  { «名称» := "MildCharityPack"
    «允许» := fun
      | .temporalFromWorldHistory => True
      | .unifiedDynamicsFromHistory => True
      | .autonomousEvolutionFromHistory => True
      | .wholeWorldFromExplicitUniverseLabel => True
      | .connectedFromCauchyLikeSlices => True
      | .weakRealistCosmology => False
    «世界覆盖说明» := fun atom =>
      s!"[MildCharityPack] no source snippet attached for {reprStr atom}; keep the assertion but mark it as minimally charitable."
    «配对覆盖说明» := fun atom =>
      s!"[MildCharityPack] no source snippet attached for {reprStr atom}; keep the assertion but mark it as minimally charitable."
    «宇宙族覆盖说明» := fun atom =>
      s!"[MildCharityPack] no source snippet attached for {reprStr atom}; keep the assertion but mark it as minimally charitable."
    «攻击覆盖说明» := fun atom =>
      s!"[MildCharityPack] no source snippet attached for {reprStr atom}; keep the assertion but mark it as minimally charitable." }

def RealistSciFiPack : AssumptionPack :=
  { «名称» := "RealistSciFiPack"
    «允许» := fun
      | .temporalFromWorldHistory => True
      | .unifiedDynamicsFromHistory => True
      | .autonomousEvolutionFromHistory => True
      | .wholeWorldFromExplicitUniverseLabel => True
      | .connectedFromCauchyLikeSlices => True
      | .weakRealistCosmology => True
    «世界覆盖说明» := fun atom =>
      s!"[RealistSciFiPack] no source snippet attached for {reprStr atom}; only weak realist-physics bridges are allowed here, not a full cosmology completion."
    «配对覆盖说明» := fun atom =>
      s!"[RealistSciFiPack] no source snippet attached for {reprStr atom}; only explicit pairwise independence facts count here."
    «宇宙族覆盖说明» := fun atom =>
      s!"[RealistSciFiPack] no source snippet attached for {reprStr atom}; family-level support still requires explicit multiplicity or completeness language."
    «攻击覆盖说明» := fun atom =>
      s!"[RealistSciFiPack] no source snippet attached for {reprStr atom}; destruction levels still require explicit attack-layer evidence." }

theorem mild_extends_conservative :
    AssumptionPack.Extends MildCharityPack ConservativePack := by
  intro flag h
  cases h

theorem realist_extends_mild :
    AssumptionPack.Extends RealistSciFiPack MildCharityPack := by
  intro flag h
  cases flag <;> simp [RealistSciFiPack, MildCharityPack] at h ⊢

theorem realistSciFiPack_enables_only_declared_flags
    (flag : AssumptionFlag) :
    RealistSciFiPack.«允许» flag ↔
      flag = .temporalFromWorldHistory ∨
      flag = .unifiedDynamicsFromHistory ∨
      flag = .autonomousEvolutionFromHistory ∨
      flag = .wholeWorldFromExplicitUniverseLabel ∨
      flag = .connectedFromCauchyLikeSlices ∨
      flag = .weakRealistCosmology := by
  cases flag <;> simp [RealistSciFiPack]

abbrev «保守包» := ConservativePack
abbrev «温和宽容包» := MildCharityPack
abbrev «写实科幻包» := RealistSciFiPack

end VerseFramework
