module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Fiber.Localization
public import stacks_project.Chap38.Lemma_38_13_3
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x y

namespace weaklyAssociatedPrimes.Fiber

/- Lemma 38.13.4: if `R → S` is essentially of finite type and the `R`-flat
`S`-module `N` is a localization of a finite `S`-module, then the weakly associated
primes of `N ⊗[R] M` are the images of the associated primes of its fibers over
the weakly associated primes of `M`. -/
@[stacks 05II]
#check
  (weaklyAssociatedPrimes.Fiber.tensorProduct_eq_iUnion_associatedPrimes :
    ∀ {R : Type u} {S : Type v} {M : Type w} {N₀ : Type x} {N : Type y}
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
      [AddCommGroup M] [Module R M]
      [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
      [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
      [Module.Flat R N]
      (T : Submonoid S) (ι : N₀ →ₗ[S] N) [IsLocalizedModule T ι],
      PrimeSpectrum.asIdeal ⁻¹' weaklyAssociatedPrimes S (N ⊗[R] M) =
        ⋃ p : PrimeSpectrum R,
          ⋃ (_ : p.asIdeal ∈ weaklyAssociatedPrimes R M),
            Ideal.Fiber.supportPoint p ''
              (PrimeSpectrum.asIdeal ⁻¹'
                associatedPrimesOfModule (p.asIdeal.Fiber S)
                  ((p.asIdeal.Fiber S) ⊗[S] N)))

/- The pointwise membership criterion underlying the fiberwise equality. -/
#check
  (weaklyAssociatedPrimes.Fiber.mem_tensorProduct_iff_of_isLocalizedModule :
    ∀ {R : Type u} {S : Type v} {M : Type w} {N₀ : Type x} {N : Type y}
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
      [AddCommGroup M] [Module R M]
      [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
      [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
      [Module.Flat R N]
      (T : Submonoid S) (ι : N₀ →ₗ[S] N) [IsLocalizedModule T ι]
      (q : PrimeSpectrum S),
      q.asIdeal ∈ weaklyAssociatedPrimes S (N ⊗[R] M) ↔
        q.asIdeal.under R ∈ weaklyAssociatedPrimes R M ∧
          (fiberPrimeAt R S q).asIdeal ∈
            associatedPrimesOfModule ((q.asIdeal.under R).Fiber S)
              (((q.asIdeal.under R).Fiber S) ⊗[S] N))

end weaklyAssociatedPrimes.Fiber
