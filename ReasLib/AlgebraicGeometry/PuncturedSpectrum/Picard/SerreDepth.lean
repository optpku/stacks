/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CanonicalExistence
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Order.WithBotTop

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- For a Noetherian local ring with a canonical dualizing complex, complete along a
regular element in its maximal ideal, every Picard class on the punctured principal
closed fiber extends to an open neighborhood in the ambient punctured spectrum if
third maximal-ideal local cohomology of the closed fiber vanishes and either the
localization satisfies `(S₂)` with minimal-prime quotient dimension at least four,
or the primewise depth-plus-dimension bound is strictly greater than three. -/
theorem picardNeighborhoodRestriction_surjective_of_serreOrDepth
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    [IsAdicComplete (Ideal.span {f}) A]
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    (h_alternative :
      (SerreConditionS (Localization.Away f) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            f ∉ p.asIdeal →
              (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus ({f} : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus ({f} : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal))))
    (h_h3 : IsZero
      ((localCohomology (IsLocalRing.maximalIdeal A) 3).obj
        (ModuleCat.of A
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))) :
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := puncturedOpen A
    let closedFiber := (quotientMap ⁻¹ᵁ punctured).toScheme
    ∀ x : Scheme.PicardGroup closedFiber,
      ∃ (V : punctured.toScheme.Opens)
        (j : closedFiber ⟶ V.toScheme),
        j ≫ V.ι = quotientMap ∣_ punctured ∧
          ∃ y : Scheme.PicardGroup V.toScheme,
            Scheme.Hom.picardPullback j y = x := sorry

end AlgebraicGeometry.PuncturedSpectrum
