/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite Relations in Tensor Products

@stack 04VX

A coefficient-matrix description of finitely supported relations in a tensor product.
-/

open scoped TensorProduct
open Finsupp Submodule

universe u v w x y

namespace TensorProduct

/-- Lemma 10.107.10: for generating families `x` of `M` and `y` of `N`, a finitely supported
relation `∑ j, m j ⊗ y j = 0` is equivalent to a finitely supported coefficient matrix whose rows
express the `m j` in terms of `x` and whose columns are relations among the `y j`. -/
@[stacks 04VX]
theorem finsupp_sum_tmul_eq_zero_iff_exists_generator_matrix
    {R : Type u} {M : Type v} {N : Type w} {I : Type x} {J : Type y}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : I → M) (y : J → N) (m : J →₀ M)
    (hx : span R (Set.range x) = ⊤) (hy : span R (Set.range y) = ⊤) :
    (m.sum (fun j mj ↦ mj ⊗ₜ[R] y j) = (0 : M ⊗[R] N)) ↔
      ∃ a : J →₀ I →₀ R,
        (∀ j, m j = linearCombination R x (a j)) ∧
          ∀ i, a.sum (fun j aij ↦ aij i • y j) = 0 := sorry

end TensorProduct
