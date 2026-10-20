module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
public import ReasLib.RingTheory.RingHom.Fiber.Module

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

namespace weaklyAssociatedPrimes.Fiber

/-- For a finitely presented ring map and a finitely presented module flat over the base,
a prime is weakly associated to a tensor product exactly when its contraction is weakly
associated to the base module and its fiber prime is associated to the fiber module. -/
@[stacks 05IG]
theorem mem_tensorProduct_iff
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    q.asIdeal ∈ weaklyAssociatedPrimes S (N ⊗[R] M) ↔
      p.asIdeal ∈ weaklyAssociatedPrimes R M ∧
        (PrimeSpectrum.fiberPrime p q hq).asIdeal ∈
          associatedPrimesOfModule (p.asIdeal.Fiber S)
            ((p.asIdeal.Fiber S) ⊗[S] N) := sorry

end weaklyAssociatedPrimes.Fiber
