/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Localization

@[expose] public section

/-!
# Source-Facing Inverse-Adjoining Charts

@stack 00ST

The reusable principal-chart results live in
`Algebra.Presentation.RelativeGlobal`.  This file retains only the literal
inverse-adjoining quotient form required by Lemma 10.136.10.
-/

open MvPolynomial
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)

-- Local declaration justification (source-local notation): these names keep the inverse-adjoining
-- polynomial presentation readable; the reusable owner is `Algebra.Presentation` in ReasLib.
local notation "PresentedIdeal" =>
  Ideal.span (Set.range f)

local notation "PresentedAlgebra" =>
  MvPolynomial (Fin n) R ⧸ PresentedIdeal

local notation "LocalizedPresentedAlgebra" =>
  fun h : MvPolynomial (Fin n) R ↦
    MvPolynomial (Fin (n + 1)) R ⧸
      Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1})

namespace Algebra.Presentation.Naive

/-- Lemma 10.136.10 (1): if all fibers over a closed base subscheme have the
expected dimension, then an inverse-adjoining presentation defines a relative
global complete-intersection principal chart which is the identity modulo the
closed subscheme. -/
@[stacks 00ST]
theorem exists_localizationAway_of_fiberDimension_on_closedSet
    (hcard : c ≤ n) (I : Ideal R)
    (hdim : ∀ p : PrimeSpectrum R,
      I ≤ p.asIdeal →
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
          ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (e : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        Ideal.Quotient.mk (Ideal.map (algebraMap R PresentedAlgebra) I) g = 1 ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

/-- Lemma 10.136.10 (2): an expected-dimension fiber has an
inverse-adjoining presentation of a relative global complete-intersection
principal chart whose generator is a unit on that fiber. -/
@[stacks 00ST]
theorem exists_localizationAway_of_fiberDimension_atPrime
    (hcard : c ≤ n) (p : PrimeSpectrum R)
    (hdim : ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (e : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber PresentedAlgebra) ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

/-- Lemma 10.136.10 (3): expected relative dimension at a target prime gives
an inverse-adjoining relative global complete-intersection principal
neighborhood of that prime. -/
@[stacks 00ST]
theorem exists_localizationAway_of_relativeDimensionAt
    (hcard : c ≤ n) (q : PrimeSpectrum PresentedAlgebra)
    (hdim : relativeDimensionAt R PresentedAlgebra q = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (e : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        g ∉ q.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

end Algebra.Presentation.Naive

end

#check @Algebra.Presentation.RelativeGlobal.exists_localizationAway_of_fiberDimension_on_closedSet
#check @Algebra.Presentation.Naive.exists_localizationAway_of_fiberDimension_on_closedSet
#check @Algebra.Presentation.Naive.exists_localizationAway_of_fiberDimension_atPrime
#check @Algebra.Presentation.Naive.exists_localizationAway_of_relativeDimensionAt
