module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Finiteness
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/- Lemma 51.7.4: finiteness of supported cohomology through degree `n` for the
regular module transfers to every finite module which is finite locally free after
localization at each element of the supporting ideal. -/
@[stacks 0BPY] #check
  (CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_of_finiteLocallyFreeAway :
    ∀ {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (n : ℕ)
    (hA : ∀ i : ℕ, i ≤ n →
      Module.Finite A
        (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A A)) (i : ℤ)))
    (hM : ∀ f ∈ I,
      Module.FiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M)),
    ∀ i : ℕ, i ≤ n →
      Module.Finite A
        (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)))

end CategoryTheory.ModuleCat.SupportedOn
