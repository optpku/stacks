/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalCohomology.Gorenstein
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace Module.LocalCohomology

/- Lemma 51.11.5 (1): for a Gorenstein Noetherian local ring and a finite module,
the local cohomology supported on `V(I)` is finite in every natural degree below
the extended-valued local-cohomology cutoff, including an infinite cutoff. -/
@[stacks 0BJU] #check
  (Module.LocalCohomology.cohomology_finite_of_lt_cutoff :
    ∀ {A M : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
      (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M],
      ∀ i : ℕ, (.some (i : ℕ∞) : WithBot ℕ∞) < cutoff I M →
        Module.Finite A
          (ModuleCat.SupportedOn.cohomology
            (PrimeSpectrum.zeroLocus (I : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)))

/- Lemma 51.11.5 (2): for a Gorenstein Noetherian local ring and a finite module,
the local cohomology supported on `V(I)` is not finite in the natural degree `s`
realizing the local-cohomology cutoff. -/
@[stacks 0BJU] #check
  (Module.LocalCohomology.cohomology_not_finite_of_cutoff :
    ∀ {A M : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
      (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (s : ℕ), cutoff I M = (.some (s : ℕ∞) : WithBot ℕ∞) →
      ¬ Module.Finite A
        (ModuleCat.SupportedOn.cohomology
          (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (s : ℤ)))

end Module.LocalCohomology
