module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.RingTheory.Ideal.AssociatedPrime.BaseChange.Flat
public import ReasLib.RingTheory.Ideal.AssociatedPrime.BaseChange.Flat.Contraction
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Relative

@[expose] public section

open scoped TensorProduct

universe u v w z

namespace AdicCompletion

/-- If every associated prime of `N ⊗[R] Q`, for every finite `R`-module `Q`, avoids the
extension of `I` to `S`, then the canonical map from `N` to its `I`-adic completion is
universally injective over `R`. -/
theorem of_universallyInjective_of_associatedPrimes
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (I : Ideal R)
    (h_ass : ∀ (Q : Type z) [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
      (q : Ideal S), q ∈ associatedPrimesOfModule S (N ⊗[R] Q) →
        I.map (algebraMap R S) + q ≠ ⊤) :
    LinearMap.UniversallyInjective.{u, w, w, z} (of I N) := sorry

/-- If every prime in the relative assassin of a finite module flat over the base avoids the
extension of `I`, then the canonical map to its `I`-adic completion is universally injective. -/
theorem of_universallyInjective_of_relativeAssassin
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite S N] [Module.Flat R N] (I : Ideal R)
    (h_ass : ∀ q : PrimeSpectrum S, q ∈ relativeAssassin R S N →
      I.map (algebraMap R S) + q.asIdeal ≠ ⊤) :
    LinearMap.UniversallyInjective.{u, w, w, z} (of I N) := sorry

end AdicCompletion
