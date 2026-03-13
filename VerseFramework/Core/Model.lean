namespace VerseFramework

universe u

abbrev WorldId := String
abbrev AttackId := String
abbrev FamilyId := String
abbrev AggregateId := String

abbrev «世界标识» := WorldId
abbrev «攻击标识» := AttackId
abbrev «宇宙族标识» := FamilyId
abbrev «聚合标识» := AggregateId

inductive TargetRef where
  | world (world : WorldId)
  | family (family : FamilyId)
  | aggregate (aggregate : AggregateId)
  deriving DecidableEq, Repr

abbrev «攻击目标» := TargetRef

structure UniverseFamily where
  «名称» : FamilyId
  «成员» : WorldId → Prop

namespace UniverseFamily

abbrev name := UniverseFamily.«名称»
abbrev member := UniverseFamily.«成员»

end UniverseFamily

abbrev «宇宙族» := UniverseFamily

-- Lightweight carrier for the five-tuple (M, g, Phi, B, C).
structure UniverseModel where
  «名称» : WorldId
  «时空» : Type u
  «几何» : Type u
  «场» : Type u
  «边界数据» : Type u
  «切片类» : Type u

namespace UniverseModel

abbrev name := UniverseModel.«名称»
abbrev spacetime := UniverseModel.«时空»
abbrev geometry := UniverseModel.«几何»
abbrev fields := UniverseModel.«场»
abbrev boundaryData := UniverseModel.«边界数据»
abbrev sliceClass := UniverseModel.«切片类»

end UniverseModel

abbrev «宇宙模型» := UniverseModel

structure Attack where
  «名称» : AttackId
  «目标» : TargetRef
  «描述» : String := ""

namespace Attack

abbrev name := Attack.«名称»
abbrev target := Attack.«目标»
abbrev description := Attack.«描述»

end Attack

abbrev «破坏» := Attack

namespace «破坏对象»

abbrev «世界» := TargetRef.world
abbrev «宇宙族» := TargetRef.family
abbrev «聚合» := TargetRef.aggregate

end «破坏对象»

end VerseFramework
