/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.FiniteLengthQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

/- Lemma 47.16.9: if `I` is a finite-length ideal contained in the maximal ideal of a
Noetherian local ring `A`, then derived coextension of a normalized dualizing complex to
`A ⧸ I` is normalized dualizing and, after restriction to `D(A)`, occurs in a distinguished
triangle with `ModuleCat.single0 (ModuleCat.of A (I →ₗ[A] E))`. -/
@[stacks 0A7S] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.finiteLengthQuotientTriangle :
    ∀ (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      (I : Ideal A) (hImax : I ≤ IsLocalRing.maximalIdeal A) (hIlen : IsFiniteLength A I)
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} (A ⧸ I)))]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} (A ⧸ I))))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull),
      letI : IsLocalRing (A ⧸ I) := IsLocalRing.quotient_of_le_maximalIdeal I hImax
      let q := Ideal.Quotient.mk I
      let ωB := (ModuleCat.derivedCoextensionOfScalars q).obj ωA
      ωB.IsNormalizedDualizingComplex HB ∧
        ∃ β : ωA ⟶ ModuleCat.single0 (ModuleCat.of A (I →ₗ[A] E)),
          ∃ δ : ModuleCat.single0 (ModuleCat.of A (I →ₗ[A] E)) ⟶
            ((ModuleCat.derivedRestrictionOfScalars q).obj ωB)⟦(1 : ℤ)⟧,
            Triangle.mk ((ModuleCat.derivedRestrictionCoextensionAdjunction q).counit.app ωA)
              β δ ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
