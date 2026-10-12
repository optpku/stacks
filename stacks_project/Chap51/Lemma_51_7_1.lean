/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Finiteness
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 51.7.1 -/
@[stacks 0AW8]
#check (CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_iff_exists_annihilator :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ),
    ((∀ i : ℕ, i ≤ n →
      Module.Finite A
        (CategoryTheory.ModuleCat.SupportedOn.cohomology T
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
        ∀ i : ℕ, i ≤ n →
          J ≤ Module.annihilator A
            (CategoryTheory.ModuleCat.SupportedOn.cohomology T
              (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))))

#check (CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_iff_exists_power_annihilator :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ),
    ((∀ i : ℕ, i ≤ n →
      Module.Finite A
        (CategoryTheory.ModuleCat.SupportedOn.cohomology
          (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∃ e : ℕ, ∀ i : ℕ, i ≤ n →
        I ^ e ≤ Module.annihilator A
          (CategoryTheory.ModuleCat.SupportedOn.cohomology
            (PrimeSpectrum.zeroLocus (I : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))))
