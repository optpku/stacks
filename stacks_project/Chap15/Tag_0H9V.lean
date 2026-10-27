/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Dimension.GenericRank
import StacksCheckRecall

@[expose] public section

open Module

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/- Lemma (0H9V): A linear map over a domain with torsion kernel and cokernel
preserves cardinal module rank. -/
@[stacks 0H9V] #check
  (Module.rank_eq_of_isTorsion_ker_coker : ∀ (f : M →ₗ[R] N)
    (hker : IsTorsion R (LinearMap.ker f))
    (hcoker : IsTorsion R (N ⧸ LinearMap.range f)),
    Module.rank R M = Module.rank R N)
