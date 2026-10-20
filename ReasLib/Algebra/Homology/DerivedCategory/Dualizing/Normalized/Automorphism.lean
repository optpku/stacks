/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/-- The canonical monoid homomorphism from scalar units to automorphisms of a derived object. -/
def scalarUnitsToAut
    (A : Type u) [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (ω : DerivedCategory (ModuleCat.{u} A)) : Aˣ →* Aut ω :=
  (Aut.unitsEndEquivAut ω).toMonoidHom.comp
    (Units.map (algebraMap A (End ω)).toMonoidHom)

namespace IsNormalizedDualizingComplex

/-- Scalar units act bijectively on a normalized dualizing complex. -/
theorem scalarUnitsToAut_bijective
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex H) :
    Function.Bijective (DerivedCategory.scalarUnitsToAut A ω) := sorry

end IsNormalizedDualizingComplex

end CategoryTheory.DerivedCategory
