/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness of Algebra--Module Tensor Products

This leaf supplies the canonical finiteness instance for `N ⊗[R] M` when
`N` is finite over an `R`-algebra `S` and `M` is finite over `R`.
-/

@[expose] public section

open scoped TensorProduct

namespace Module.Finite

universe u v w x

/-- A tensor product of a finite `S`-module with a finite `R`-module is finite
over `S` through the canonical algebra--tensor-module action. -/
instance tensorProduct_algebraTensorModule
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] :
    Module.Finite S (N ⊗[R] M) := by
  exact Module.Finite.equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M)

end Module.Finite
