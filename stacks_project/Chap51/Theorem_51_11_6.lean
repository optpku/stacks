module

public import ReasLib.RingTheory.LocalCohomology.FormalFibers
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace Module.LocalCohomology

/- Theorem 51.11.6 (1): if `A` is universally catenary and the formal fibers of
all its local rings are Cohen--Macaulay, then the local cohomology of a finite
`A`-module supported on `V(I)` is finite in every degree below its natural cutoff. -/
@[stacks 0BJV] #check
  (Module.LocalCohomology.cohomology_finite_of_lt_cutoff_of_formalFibers :
    ∀ {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
      (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M],
      (∀ p : PrimeSpectrum A,
        FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
          (Localization.AtPrime p.asIdeal)) →
      ∀ i : ℕ, (.some (i : ℕ∞) : WithBot ℕ∞) < cutoff I M →
        Module.Finite A
          (ModuleCat.SupportedOn.cohomology
            (PrimeSpectrum.zeroLocus (I : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)))

/- Theorem 51.11.6 (2): under the same universal-catenarity and Cohen--Macaulay
formal-fiber assumptions, local cohomology supported on `V(I)` is not finite in
the natural degree realizing the cutoff. -/
@[stacks 0BJV] #check
  (Module.LocalCohomology.cohomology_not_finite_of_cutoff_of_formalFibers :
    ∀ {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
      (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (s : ℕ), cutoff I M = (.some (s : ℕ∞) : WithBot ℕ∞) →
      (∀ p : PrimeSpectrum A,
        FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
          (Localization.AtPrime p.asIdeal)) →
      ¬ Module.Finite A
        (ModuleCat.SupportedOn.cohomology
          (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (s : ℤ)))

end Module.LocalCohomology
