/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

open TensorProduct

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Module.FiniteLocallyFree

/-- The tensor product of finite locally free modules is finite locally free. -/
instance tensorProduct [FiniteLocallyFree R M] [FiniteLocallyFree R N] :
    FiniteLocallyFree R (M ⊗[R] N) := sorry

end Module.FiniteLocallyFree

namespace Module.FiniteLocallyFreeOfRank

/-- The tensor product of finite locally free modules of rank one is finite locally free of rank one. -/
instance tensorProduct [FiniteLocallyFreeOfRank R M 1] [FiniteLocallyFreeOfRank R N 1] :
    FiniteLocallyFreeOfRank R (M ⊗[R] N) 1 := sorry

end Module.FiniteLocallyFreeOfRank
