/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Finiteness
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/- Lemma 51.7.2 -/
@[stacks 0AW9] #check
  (CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_iff_localizedAtPrime_finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ),
      ((∀ i : ℕ, i ≤ n →
          Module.Finite A
            (CategoryTheory.ModuleCat.SupportedOn.cohomology
              (PrimeSpectrum.zeroLocus (I : Set A))
              (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
        ∀ (p : PrimeSpectrum A) (i : ℕ), i ≤ n →
          Module.Finite (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal
              (CategoryTheory.ModuleCat.SupportedOn.cohomology
                (PrimeSpectrum.zeroLocus (I : Set A))
                (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)))))

end CategoryTheory.ModuleCat.SupportedOn
