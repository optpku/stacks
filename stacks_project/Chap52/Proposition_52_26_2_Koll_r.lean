/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.RingTheory.Depth
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTripleSetup

/-- The depth bound for the quotient by a regular element is equivalent to the
depth bound one higher on the original local ring. -/
theorem depth_quotient_ge_two_iff_depth_ge_three
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    ((2 : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span ({f} : Set A))) ↔
      ((3 : ℕ∞) ≤ moduleDepth A A) := sorry

/-- Proposition 52.26.2 (Kollár) (1): under the dualizing, regularity, depth,
and primewise hypotheses, restriction from the punctured spectrum to the
punctured closed fiber is injective on Picard groups. -/
@[stacks 0F2B]
theorem picardPullback_injective_of_dualizing_depth
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (h_depth : (3 : ℕ∞) ≤ moduleDepth A A)
    (h_prime_depth : ∀ p : PrimeSpectrum A,
      f ∈ p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (2 : WithBot ℕ∞) →
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal)) :
    let S := CoherentTripleSetup.ofElement f hf_mem hf_regular
    Function.Injective (Scheme.Hom.picardPullback S.closedFiberOnU) := sorry

/-- Proposition 52.26.2 (Kollár) (2): under the first three hypotheses,
(S2), and dimension at least four, every prime containing `f` with
two-dimensional quotient has localized depth at least two. -/
@[stacks 0F2B]
theorem primeDepth_ge_two_of_s2_dimension
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (h_depth : (3 : ℕ∞) ≤ moduleDepth A A)
    [SerreConditionS A 2]
    (h_dim : (4 : WithBot ℕ∞) ≤ ringKrullDim A) :
    ∀ p : PrimeSpectrum A,
      f ∈ p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (2 : WithBot ℕ∞) →
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal) := sorry

end AlgebraicGeometry.CoherentTripleSetup
