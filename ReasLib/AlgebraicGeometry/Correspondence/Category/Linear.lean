/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.AlgebraicGeometry.Correspondence.Category

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- Degree-zero rational Chow correspondences form a preadditive category. -/
instance instPreadditive : Preadditive (Category k) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Rational X.scheme Y.scheme 0))
  add_comp := sorry
  comp_add := sorry

/-- Degree-zero rational Chow correspondences form a `ℚ`-linear category. -/
instance instLinear : Linear ℚ (Category k) where
  homModule := fun X Y ↦ inferInstanceAs (Module ℚ (Rational X.scheme Y.scheme 0))
  smul_comp := sorry
  comp_smul := sorry

end AlgebraicGeometry.Correspondence
