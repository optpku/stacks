/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalCohomology.FormalFibers
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

/- Remark 51.11.7 (1): if `A` is universally catenary, the cutoff is strictly
above `n`, and every formal fiber of every local ring of `A` satisfies `(S_n)`,
then local cohomology supported on `V(I)` is finite in every degree at most `n`. -/
@[stacks 0BJW] #check
  (Module.LocalCohomology.cohomology_finite_of_le_cutoff_of_serreFormalFibers :
    ∀ {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
      (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (n : ℕ)
      (h_cutoff : (.some (n : ℕ∞) : WithBot ℕ∞) < Module.LocalCohomology.cutoff I M)
      (h_formal : ∀ p : PrimeSpectrum A,
        (FieldAlgebraProperty.serreConditionS n).HoldsOnFormalFibers
          (Localization.AtPrime p.asIdeal)),
      ∀ i : ℕ, i ≤ n →
        Module.Finite A
          (ModuleCat.SupportedOn.cohomology
            (PrimeSpectrum.zeroLocus (I : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)))

/- Remark 51.11.7 (2): if the cutoff is realized by `s` and every formal fiber
of every local ring of `A` satisfies `(S_{s - 1})`, then local cohomology
supported on `V(I)` is not finite in degree `s`. -/
@[stacks 0BJW] #check
  (Module.LocalCohomology.cohomology_not_finite_of_cutoff_of_serreFormalFibers :
    ∀ {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
      (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (s : ℕ)
      (hs : Module.LocalCohomology.cutoff I M = (.some (s : ℕ∞) : WithBot ℕ∞))
      (h_formal : ∀ p : PrimeSpectrum A,
        (FieldAlgebraProperty.serreConditionS (s - 1)).HoldsOnFormalFibers
          (Localization.AtPrime p.asIdeal)),
      ¬ Module.Finite A
        (ModuleCat.SupportedOn.cohomology
          (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (s : ℤ)))
