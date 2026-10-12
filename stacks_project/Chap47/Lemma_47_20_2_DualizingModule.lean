/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.DualizingModule

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/- The dualizing module datum is provided by the normalized dualizing-complex library owner. -/
#check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.dualizingModule :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex H), ModuleCat.{u} A)

/- The dimension-specialized computation for the dualizing module is provided by the
normalized dualizing-complex library owner. -/
#check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.dualizingModule_eq_of_krullDim :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex H)
    (d : ℕ) (hd : ringKrullDim A = d),
    dualizingModule H ω hω =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj ω)

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

end
