/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Finiteness
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

open CategoryTheory
open DerivedCategory.Plus.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/-- Supported cohomology of a bounded-below coherent complex is finite through degree
`n` exactly when an ideal whose zero locus lies in `T` annihilates every such degree. -/
theorem cohomology_finite_iff_exists_annihilator_of_boundedBelow
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : D⁺[ModuleCat.isFinitePresentation A]) (n : ℤ) :
    (∀ i : ℤ, i ≤ n →
      Module.Finite A
        (cohomology T
          ((ambient (ModuleCat.isFinitePresentation A)).obj K) i)) ↔
      ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
        ∀ i : ℤ, i ≤ n →
          J ≤ Module.annihilator A
            (cohomology T
              ((ambient (ModuleCat.isFinitePresentation A)).obj K) i) := sorry

/-- For closed support `V(I)`, supported cohomology of a bounded-below coherent
complex is finite through degree `n` exactly when one power of `I` annihilates every
such degree. -/
theorem cohomology_finite_iff_exists_power_annihilator_of_boundedBelow
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : D⁺[ModuleCat.isFinitePresentation A]) (n : ℤ) :
    (∀ i : ℤ, i ≤ n →
      Module.Finite A
        (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          ((ambient (ModuleCat.isFinitePresentation A)).obj K) i)) ↔
      ∃ e : ℕ, ∀ i : ℤ, i ≤ n →
        I ^ e ≤ Module.annihilator A
          (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
            ((ambient (ModuleCat.isFinitePresentation A)).obj K) i) := sorry

end CategoryTheory.ModuleCat.SupportedOn
