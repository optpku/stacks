module

public import ReasLib.Algebra.Module.DirectSumDevissage.FinitePresentation
public import ReasLib.RingTheory.Ideal.AssociatedPrime.DirectSum

@[expose] public section

/-!
# Exact associated primes over Henselian local rings

This module records how exact associated primes of tensor products interact
with the maximal ideal of a Henselian local base ring.
-/

open scoped DirectSum TensorProduct Algebra.TensorProduct.Right

universe u v w x

namespace associatedPrimesOfModule.Henselian

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]
variable {M : Type x} [AddCommGroup M] [Module R M]

/-- Over a Henselian local ring, an exact associated prime of `N ⊗[R] M`
remains proper after adding the extension of the maximal ideal, provided that
`N` is countably generated and Mittag-Leffler over the base ring. -/
@[stacks 05IV]
theorem add_map_maximalIdeal_ne_top
    (hcg : Module.CountablyGenerated R N)
    (hML : Module.MittagLeffler R N)
    {q : Ideal S}
    (hq : q ∈ _root_.associatedPrimesOfModule S (N ⊗[R] M)) :
    q + Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≠ ⊤ := sorry

end associatedPrimesOfModule.Henselian
