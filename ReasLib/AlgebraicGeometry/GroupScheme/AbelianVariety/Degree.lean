module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Dimension
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.MulBy
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Degrees of multiplication maps on abelian varieties
-/

@[expose] public section

open CategoryTheory
open scoped AbelianVariety

universe u

namespace AlgebraicGeometry.AbelianVariety

variable {k : Type u} [Field k]

/-- Multiplication by `d ≠ 0` on an abelian variety of dimension `g` is finite locally free
of rank `d ^ (2 * g)`. -/
instance instIsFiniteLocallyFreeOfRankMulBy (A : SchemeOverField k) [GrpObj A]
    [AlgebraicGeometry.AbelianVariety A] (d : ℕ) [NeZero d] :
    IsFiniteLocallyFreeOfRank ([d]ₐ A) (d ^ (2 * dimension A)) := sorry

end AlgebraicGeometry.AbelianVariety
