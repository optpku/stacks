/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-kernel factorization through finitely presented modules

This leaf owns the finite-presentation factorization that kills a prescribed
element of the kernel of a tensor-extended linear map.

@stack 059L
-/

@[expose] public section

open scoped TensorProduct

universe u v w z

namespace LinearMap

/-- Lemma 10.89.4: if a tensor element dies under a map from a finitely
presented module, the map factors through another finitely presented module
where that element already dies. -/
@[stacks 059L]
theorem exists_finitePresentation_factorization_of_mem_ker_rTensor
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    (f : P →ₗ[R] M)
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    {x : P ⊗[R] Q} (hx : x ∈ ker (f.rTensor Q)) :
    ∃ (P' : ModuleCat.{max u w} R) (_ : Module.FinitePresentation R P')
      (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
        f = g.comp f' ∧ x ∈ ker (f'.rTensor Q) := sorry

end LinearMap
