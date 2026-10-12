/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.FiniteLocal
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteLength
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- For a finite-length ideal below the maximal ideal of a Noetherian local ring,
the derived quotient of a normalized dualizing complex is normalized and fits
with the original complex and the Matlis dual of the ideal in a distinguished
triangle. -/
theorem finiteLengthQuotientTriangle
    (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    (I : Ideal A) (hImax : I ≤ IsLocalRing.maximalIdeal A) (hIlen : IsFiniteLength A I)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (A ⧸ I)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} (A ⧸ I))))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA)
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull) :
    -- Local instance justification (proof-local temporary data): `hImax` supplies the quotient locality needed to state normalization of `ωB`.
    letI : IsLocalRing (A ⧸ I) := IsLocalRing.quotient_of_le_maximalIdeal I hImax
    let q := Ideal.Quotient.mk I
    let ωB := (ModuleCat.derivedCoextensionOfScalars q).obj ωA
    ωB.IsNormalizedDualizingComplex HB ∧
      ∃ β : ωA ⟶ ModuleCat.single0 (ModuleCat.of A (I →ₗ[A] E)),
        ∃ δ : ModuleCat.single0 (ModuleCat.of A (I →ₗ[A] E)) ⟶
          ((ModuleCat.derivedRestrictionOfScalars q).obj ωB)⟦(1 : ℤ)⟧,
          Triangle.mk ((ModuleCat.derivedRestrictionCoextensionAdjunction q).counit.app ωA)
            β δ ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
