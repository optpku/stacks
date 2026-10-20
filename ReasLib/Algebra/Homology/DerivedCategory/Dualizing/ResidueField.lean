/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteCoextension
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Uniqueness
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- For a dualizing complex over a Noetherian commutative ring, derived coextension
to the quotient by a maximal ideal is a shift of the quotient ring in the derived
category of quotient-ring modules. -/
theorem coextensionToResidueField
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)
    (m : Ideal A) (hm : m.IsMaximal) :
    ∃ n : ℤ, Nonempty
      ((ModuleCat.derivedCoextensionOfScalars (Ideal.Quotient.mk m)).obj ω ≅
        (shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⧸ m))) n).obj
          (ModuleCat.single0 (ModuleCat.of (A ⧸ m) (A ⧸ m)))) := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
