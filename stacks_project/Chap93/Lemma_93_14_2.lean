module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import stacks_project.Chap93.Lemma_93_14_2_Henselization

/-!
# Henselizing first-order extensions of a finite type algebra over a field

If `k → B` is of finite type and smooth away from `V(J)`, pair henselization
of `(B, J)` induces a bijection on first-order square-zero extensions
`Exal_k(B, N)`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra
open PrimeSpectrum
open RingPairCat

namespace Algebra.Exal

variable (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
variable [AddCommGroup N] [Module B N]
variable [henselianPairInclusion.IsRightAdjoint]

/-- Lemma 93.14.2
Let `k` be a field. Let `B` be a finite type `k`-algebra. Let `J ⊂ B` be an
ideal such that `Spec B → Spec k` is smooth on the complement of `V(J)`. Let
`N` be a finite `B`-module. Then pair henselization of `(B, J)` induces a
canonical bijection `Exal k B N → Exal k B^h N^h`, where `(B^h, J^h)` is the
henselization of `(B, J)` as `henselizationRing (pairOfIdeal J)` and
`henselizationIdeal (pairOfIdeal J)`, and `N^h = N ⊗[B] B^h`.
-/
@[stacks 0DZC]
theorem henselization_bijective [Algebra.FiniteType k B] [Module.Finite B N]
    (J : Ideal B) (hsmooth : (zeroLocus (J : Set B))ᶜ ⊆ smoothLocus k B) :
    Function.Bijective (henselization k B N J) := sorry

end Algebra.Exal
