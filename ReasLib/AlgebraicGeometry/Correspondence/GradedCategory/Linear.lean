/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Graded.DegreeZero
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.GradedCategory

variable {k : Type u} [Field k]

/-- Graded rational Chow correspondences form a preadditive category. -/
instance instPreadditive : Preadditive (GradedCategory k) where
  homGroup X Y := inferInstanceAs
    (AddCommGroup (Rational X.1.scheme Y.1.scheme (Y.2 - X.2)))
  add_comp := sorry
  comp_add := sorry

/-- Graded rational Chow correspondences form a `ℚ`-linear category. -/
instance instLinear : Linear ℚ (GradedCategory k) where
  homModule := fun X Y ↦ inferInstanceAs
    (Module ℚ (Rational X.1.scheme Y.1.scheme (Y.2 - X.2)))
  smul_comp := sorry
  comp_smul := sorry

end AlgebraicGeometry.Correspondence.GradedCategory

namespace AlgebraicGeometry.Correspondence.Graded

variable {k : Type u} [Field k]

/-- Embed degree-zero correspondences into the twist-graded category at Tate twist zero. -/
def zeroTwistFunctor (k : Type u) [Field k] :
    DegreeZero (k := k) ⥤ Correspondence.GradedCategory k where
  obj X := Correspondence.GradedCategory.ofScheme X.obj.scheme 0
  map {X Y} f := degreeZeroHomEquiv X Y f
  map_id := sorry
  map_comp := sorry

/-- The zero-twist functor places the underlying smooth projective scheme in twist zero. -/
theorem zeroTwistFunctor_obj (X : DegreeZero (k := k)) :
    (zeroTwistFunctor k).obj X =
      Correspondence.GradedCategory.ofScheme X.obj.scheme 0 := sorry

/-- The zero-twist functor sends a degree-zero morphism to its rational correspondence. -/
theorem zeroTwistFunctor_map {X Y : DegreeZero (k := k)} (f : X ⟶ Y) :
    (zeroTwistFunctor k).map f =
      degreeZeroHomEquiv X Y f := sorry

end AlgebraicGeometry.Correspondence.Graded
