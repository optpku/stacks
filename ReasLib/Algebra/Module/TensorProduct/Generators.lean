/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generating tensor products

This file records how spanning families in two modules give a spanning family of pure tensors.
The result is independent of sheaves and geometric applications.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

/-- Pairwise pure tensors of two spanning families span the tensor product. -/
@[stacks 01AO "algebraic tensor generators"]
theorem span_range_tmul_eq_top
    {R ι κ M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (m : ι → M) (n : κ → N)
    (hm : Submodule.span R (Set.range m) = ⊤)
    (hn : Submodule.span R (Set.range n) = ⊤) :
    Submodule.span R
      (Set.range fun ij : ι × κ ↦ m ij.1 ⊗ₜ[R] n ij.2) = ⊤ := sorry

end TensorProduct
