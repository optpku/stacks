/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.LocalCohomology.Cutoff
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.FinitenessCriterion

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace Module.LocalCohomology

/-- For a finite module over a Gorenstein local ring, supported local cohomology
is finite in every natural degree below the extended-valued cutoff, including
when the cutoff is infinite. -/
theorem cohomology_finite_of_lt_cutoff
    {A M : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
    (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∀ i : ℕ, (.some (i : ℕ∞) : WithBot ℕ∞) < cutoff I M →
      Module.Finite A
        (ModuleCat.SupportedOn.cohomology
          (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)) := sorry

/-- For a finite module over a Gorenstein local ring, supported local cohomology
is not finite in the natural degree realizing the cutoff. -/
theorem cohomology_not_finite_of_cutoff
    {A M : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
    (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s : ℕ)
    (hs : cutoff I M = (.some (s : ℕ∞) : WithBot ℕ∞)) :
    ¬ Module.Finite A
      (ModuleCat.SupportedOn.cohomology
        (PrimeSpectrum.zeroLocus (I : Set A))
        (ModuleCat.single0 (ModuleCat.of A M)) (s : ℤ)) := sorry

end Module.LocalCohomology
