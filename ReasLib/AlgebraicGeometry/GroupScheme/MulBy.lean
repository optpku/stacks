module

public import ReasLib.CategoryTheory.Monoidal.Grp.MulBy
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Multiplication maps of group schemes
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The multiplication-by-`n` endomorphism of the underlying scheme of a group scheme over
`k`. -/
noncomputable abbrev mulBy (A : SchemeOverField k) [GrpObj A] (n : ℕ) : A.left ⟶ A.left :=
  (CategoryTheory.GrpObj.mulBy A n).left

/-- The multiplication-by-`d` endomorphism of the underlying scheme of a group scheme over
`k`, for an integer `d`. -/
noncomputable abbrev mulByInt (A : SchemeOverField k) [GrpObj A] (d : ℤ) :
    A.left ⟶ A.left :=
  ((𝟙 A) ^ d).left

/-- Signed multiplication by a nonnegative integer agrees with the natural-number
multiplication map. -/
theorem mulByInt_natCast (A : SchemeOverField k) [GrpObj A] (n : ℕ) :
    mulByInt A (n : ℤ) = mulBy A n := sorry

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.AbelianVariety

/-- Scoped notation for the multiplication-by-`n` morphism of an abelian variety. -/
scoped[AbelianVariety] notation:max "[" n "]ₐ " A => AlgebraicGeometry.SchemeOverField.mulBy A n

end AlgebraicGeometry.AbelianVariety
