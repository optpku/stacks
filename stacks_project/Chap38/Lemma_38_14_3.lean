module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.DirectSum
import StacksCheckRecall

@[expose] public section

open scoped DirectSum TensorProduct Algebra.TensorProduct.Right

universe u v w x y z

/- Lemma 38.14.3: if the `S`-module `N` is `R`-linearly equivalent to a direct sum
of finite `R`-modules, then an exact associated prime of `N ⊗[R] M` remains proper
after adding the extension of the maximal ideal of `R` to `S`. -/
@[stacks 05IU] #check
  (associatedPrimesOfModule.DirectSum.add_map_maximalIdeal_ne_top :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      {S : Type v} [CommRing S] [Algebra R S]
      {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
      [IsScalarTower R S N]
      {M : Type x} [AddCommGroup M] [Module R M]
      {ι : Type y} {P : ι → Type z}
      [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
      [∀ i, Module.Finite R (P i)]
      (_ : Nonempty (N ≃ₗ[R] ⨁ i, P i)) {q : Ideal S},
      q ∈ associatedPrimesOfModule S (N ⊗[R] M) →
        q + Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≠ ⊤)
