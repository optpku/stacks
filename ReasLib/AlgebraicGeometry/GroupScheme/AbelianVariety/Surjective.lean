module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Degree
public import ReasLib.AlgebraicGeometry.GroupScheme.RationalPoints
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion

/-!
# Surjective multiplication maps on abelian varieties
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AbelianVariety CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AbelianVariety

variable {k : Type u} [Field k]

/-- Multiplication by a nonzero natural number on an abelian variety is surjective. -/
instance instMulBySurjective (A : SchemeOverField k) [GrpObj A] [AbelianVariety A]
    (n : ℕ) [NeZero n] : Surjective ([n]ₐ A) := sorry

variable (A : SchemeOverField k) [GrpObj A] [AbelianVariety A]

/-- Over an algebraically closed field, multiplication by a positive natural number is
surjective on the additive group of rational points of an abelian variety. -/
theorem rationalPoints_nsmul_surjective [IsAlgClosed k] (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (fun x : SchemeOverField.rationalPoints A ↦ n • x) := sorry

end AlgebraicGeometry.AbelianVariety
