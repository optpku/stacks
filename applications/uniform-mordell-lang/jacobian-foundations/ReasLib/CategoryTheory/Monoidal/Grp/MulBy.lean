module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Multiplication maps of group objects
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The multiplication-by-`n` endomorphism of a group object. -/
noncomputable abbrev mulBy (G : C) [GrpObj G] (n : ℕ) : G ⟶ G :=
  (𝟙 G) ^ n

/-- The multiplication-by-`n` endomorphism of a group object for an integer `n`. -/
noncomputable abbrev mulByInt (G : C) [GrpObj G] (n : ℤ) : G ⟶ G :=
  (𝟙 G) ^ n

/-- Signed multiplication by a natural number agrees with natural multiplication. -/
theorem mulByInt_natCast (G : C) [GrpObj G] (n : ℕ) :
    mulByInt G (n : ℤ) = mulBy G n := by
  exact zpow_natCast (𝟙 G) n

/-- A point is fixed by multiplication by `n` if and only if its `(n - 1)`st power is one. -/
theorem comp_mulByInt_eq_self_iff (G : C) [GrpObj G] (n : ℤ) {X : C} (p : X ⟶ G) :
    p ≫ mulByInt G n = p ↔ p ^ (n - 1) = 1 := by
  simp only [mulByInt, comp_zpow, Category.comp_id, zpow_sub_one, mul_inv_eq_one]

end CategoryTheory.GrpObj
