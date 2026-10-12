/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.FiniteLocal
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.RingTheory.Ideal.Principal
public import ReasLib.RingTheory.LocalRing.Quotient

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- For a regular element in the maximal ideal of a Noetherian local ring, derived
coextension to the principal quotient is normalized dualizing and forms the
distinguished triangle determined by the quotient counit and multiplication. -/
theorem regularQuotientTriangle
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A) (hf : IsRegular (f : A))
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory
      (DerivedCategory (ModuleCat.{u} (A ⧸ principalIdeal (f : A))))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed
      (DerivedCategory (ModuleCat.{u} (A ⧸ principalIdeal (f : A)))))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA) :
    let q := Ideal.Quotient.mk (principalIdeal (f : A))
    let ωB := (ModuleCat.derivedCoextensionOfScalars q).obj ωA
    ∃ δ : ωA ⟶ ((ModuleCat.derivedRestrictionOfScalars q).obj ωB)⟦(1 : ℤ)⟧,
      ωB.IsNormalizedDualizingComplex HB ∧
        Triangle.mk ((ModuleCat.derivedRestrictionCoextensionAdjunction q).counit.app ωA)
          ((f : A) • 𝟙 ωA) δ ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
