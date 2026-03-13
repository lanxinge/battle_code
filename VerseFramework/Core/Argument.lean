namespace VerseFramework

inductive ArgumentProfile where
  | monadicOnly
  | destructionQualified
  deriving DecidableEq, Repr

abbrev «论证档位» := ArgumentProfile

namespace «论证档位»

abbrev «仅单体» : «论证档位» := ArgumentProfile.monadicOnly
abbrev «破坏合格» : «论证档位» := ArgumentProfile.destructionQualified

end «论证档位»

end VerseFramework
