module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Degree

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AbelianVariety

universe u

namespace AlgebraicGeometry.AbelianVariety

#check
  (AlgebraicGeometry.AbelianVariety.dimension :
    ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
      [AlgebraicGeometry.AbelianVariety A], ℕ)

#check
  (AlgebraicGeometry.AbelianVariety.topologicalKrullDim_eq_dimension :
    ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
      [AlgebraicGeometry.AbelianVariety A],
      topologicalKrullDim A.left = AlgebraicGeometry.AbelianVariety.dimension A)

#check
  (AlgebraicGeometry.AbelianVariety.instIsFiniteLocallyFreeOfRankMulBy :
    ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
      [AlgebraicGeometry.AbelianVariety A] (d : ℕ) [NeZero d],
      IsFiniteLocallyFreeOfRank ([d]ₐ A)
        (d ^ (2 * AlgebraicGeometry.AbelianVariety.dimension A)))

end AlgebraicGeometry.AbelianVariety
