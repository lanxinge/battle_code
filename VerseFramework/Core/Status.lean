namespace VerseFramework

inductive ProofStatus where
  | proved
  | provableUnderAssumptions (packName : String)
  | underdetermined
  | refuted
  deriving DecidableEq, Repr

abbrev «证明状态» := ProofStatus

structure Verdict (Claim : Type _) where
  «断言» : Claim
  «状态» : ProofStatus
  deriving Repr

abbrev «判定» := Verdict

namespace Verdict

abbrev claim {Claim : Type _} := @Verdict.«断言» Claim
abbrev status {Claim : Type _} := @Verdict.«状态» Claim

end Verdict

namespace «证明状态»

abbrev «已证明» : «证明状态» := ProofStatus.proved
abbrev «证据不足» : «证明状态» := ProofStatus.underdetermined
abbrev «已反驳» : «证明状态» := ProofStatus.refuted
abbrev «在假设下可证明» := ProofStatus.provableUnderAssumptions

end «证明状态»

end VerseFramework
