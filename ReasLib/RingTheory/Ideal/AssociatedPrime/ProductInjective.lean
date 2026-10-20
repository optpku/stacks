module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Associated-prime localization product

@stack 0311

The product map indexed by `associatedPrimes R M` is a reusable module-level
injectivity criterion.  It is kept separate from the localization-set
equalities so that consumers need only the product-map statement.
-/

universe u v w

namespace associatedPrimes

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.63.19 (0311): localizations at all associated primes detect every
element of a Noetherian module.  The product is the canonical `LinearMap.pi`
over the bundled associated-prime index, so this owner exposes no extra map
data or witness choices. -/
@[stacks 0311 "associated-prime localization product injectivity"]
theorem localizationProduct_injective :
    Function.Injective
      (LinearMap.pi fun p : associatedPrimes R M ↦
        LocalizedModule.mkLinearMap p.1.primeCompl M) := sorry

/-- Lemma 15.23.12 (0AV7): a module map is injective when its localization is injective at every
associated prime of the source. -/
@[stacks 0AV7 "associated-prime local injectivity criterion"]
theorem injective_of_localized_injective
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (h : ∀ p : associatedPrimes R M,
      Function.Injective (LocalizedModule.map p.1.primeCompl f)) :
    Function.Injective f := sorry

/-- The primewise disjunction form of the associated-prime injectivity criterion. -/
@[stacks 0AV7 "primewise associated-prime injectivity criterion"]
theorem injective_of_localized_injective_or_not_mem_associatedPrimes
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R,
      Function.Injective (LocalizedModule.map p.asIdeal.primeCompl f) ∨
        p.asIdeal ∉ associatedPrimes R M) :
    Function.Injective f := sorry

end associatedPrimes

end
