/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.TensorProduct
import StacksCheckRecall

@[expose] public section

open TensorProduct

universe u v w

/- Exercise 111.22.2 (1): the tensor product of finite locally free modules is finite
locally free. -/
@[stacks 078P]
#check (Module.FiniteLocallyFree.tensorProduct :
  ∀ {R : Type u} {M : Type v} {N : Type w} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] [Module.FiniteLocallyFree R M]
    [Module.FiniteLocallyFree R N], Module.FiniteLocallyFree R (M ⊗[R] N))

/- Exercise 111.22.2 (2): the tensor product of two invertible modules is invertible. -/
@[stacks 078P]
#check (Module.FiniteLocallyFreeOfRank.tensorProduct :
  ∀ {R : Type u} {M : Type v} {N : Type w} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N]
    [Module.FiniteLocallyFreeOfRank R M 1] [Module.FiniteLocallyFreeOfRank R N 1],
    Module.FiniteLocallyFreeOfRank R (M ⊗[R] N) 1)
