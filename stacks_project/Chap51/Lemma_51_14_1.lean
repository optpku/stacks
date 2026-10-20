/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.DerivedFiniteness
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ModuleCat.SupportedOn
open DerivedCategory.Plus.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe u

/- Lemma 51.14.1 (1): for a specialization-stable subset `T` of `Spec(A)`, supported
cohomology of a bounded-below coherent complex is finite through degree `n` exactly when
one ideal whose zero locus lies in `T` annihilates every such degree. -/
@[stacks 0EI1]
#check
(CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_iff_exists_annihilator_of_boundedBelow :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
      (K : D⁺[ModuleCat.isFinitePresentation A]) (n : ℤ),
      (∀ i : ℤ, i ≤ n →
        Module.Finite A
          (cohomology T
            ((ambient (ModuleCat.isFinitePresentation A)).obj K) i)) ↔
        ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
          ∀ i : ℤ, i ≤ n →
            J ≤ Module.annihilator A
              (cohomology T
                ((ambient (ModuleCat.isFinitePresentation A)).obj K) i))

/- Lemma 51.14.1 (2): for support `V(I)`, supported cohomology of a bounded-below
coherent complex is finite through degree `n` exactly when one power of `I` annihilates
every such degree. -/
@[stacks 0EI1]
#check
(CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_iff_exists_power_annihilator_of_boundedBelow :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (K : D⁺[ModuleCat.isFinitePresentation A]) (n : ℤ),
      (∀ i : ℤ, i ≤ n →
        Module.Finite A
          (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
            ((ambient (ModuleCat.isFinitePresentation A)).obj K) i)) ↔
        ∃ e : ℕ, ∀ i : ℤ, i ≤ n →
          I ^ e ≤ Module.annihilator A
            (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
              ((ambient (ModuleCat.isFinitePresentation A)).obj K) i))
