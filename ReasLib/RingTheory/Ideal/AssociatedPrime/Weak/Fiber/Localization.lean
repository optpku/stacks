/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Fiber

/-!
# Weakly associated primes of tensor products with localized finite modules

This module describes the weakly associated primes of a tensor product with a flat module
presented as a localization of a finite module over an essentially finite type algebra.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x y

namespace weaklyAssociatedPrimes.Fiber

/-- Membership in the fiberwise description of the weakly associated primes of
`N ⊗[R] M`, expressed using contraction and the canonical prime in the fiber. -/
theorem mem_tensorProduct_iff_of_isLocalizedModule
    {R : Type u} {S : Type v} {M : Type w} {N₀ : Type x} {N : Type y}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (T : Submonoid S) (ι : N₀ →ₗ[S] N) [IsLocalizedModule T ι]
    (q : PrimeSpectrum S) :
    q.asIdeal ∈ weaklyAssociatedPrimes S (N ⊗[R] M) ↔
      q.asIdeal.under R ∈ weaklyAssociatedPrimes R M ∧
        (fiberPrimeAt R S q).asIdeal ∈
          associatedPrimesOfModule ((q.asIdeal.under R).Fiber S)
            (((q.asIdeal.under R).Fiber S) ⊗[S] N) := sorry

/-- If an algebra is essentially of finite type and a flat module is a localization of a
finite module, then the weakly associated primes of its tensor product are the images of
the associated primes of its fibers over the weakly associated primes of the base module. -/
@[stacks 05II]
theorem tensorProduct_eq_iUnion_associatedPrimes
    {R : Type u} {S : Type v} {M : Type w} {N₀ : Type x} {N : Type y}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (T : Submonoid S) (ι : N₀ →ₗ[S] N) [IsLocalizedModule T ι] :
    PrimeSpectrum.asIdeal ⁻¹' weaklyAssociatedPrimes S (N ⊗[R] M) =
      ⋃ p : PrimeSpectrum R,
        ⋃ (_ : p.asIdeal ∈ weaklyAssociatedPrimes R M),
          Ideal.Fiber.supportPoint p ''
            (PrimeSpectrum.asIdeal ⁻¹'
              associatedPrimesOfModule (p.asIdeal.Fiber S)
                ((p.asIdeal.Fiber S) ⊗[S] N)) := sorry

end weaklyAssociatedPrimes.Fiber
