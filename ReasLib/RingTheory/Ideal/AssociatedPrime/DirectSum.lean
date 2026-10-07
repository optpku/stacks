module

public import Mathlib.Algebra.DirectSum.Module
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

/-!
# Exact Associated Primes and Direct Sums

This module records the behavior of exact associated primes for tensor products
whose first factor decomposes as a direct sum of finite modules.
-/

open scoped DirectSum TensorProduct Algebra.TensorProduct.Right

universe u v w x y z

namespace associatedPrimesOfModule.DirectSum

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {ι : Type y} {P : ι → Type z}
variable [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
variable [∀ i, Module.Finite R (P i)]

/-- If an `S`-module is `R`-linearly equivalent to a direct sum of finite
`R`-modules, then every exact associated prime of its tensor product with an
`R`-module remains proper after adding the extended maximal ideal of `R`. -/
@[stacks 05IU]
theorem add_map_maximalIdeal_ne_top
    (hN : Nonempty (N ≃ₗ[R] ⨁ i, P i)) {q : Ideal S}
    (hq : q ∈ associatedPrimesOfModule S (N ⊗[R] M)) :
    q + Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≠ ⊤ := sorry

end associatedPrimesOfModule.DirectSum
