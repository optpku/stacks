/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Dimension.GenericRank
import StacksCheckRecall

@[expose] public section

universe u

open scoped TensorProduct

/- Lemma (0H9X) (1): Over a domain R, the rank of M ⊗[R] N is the product
of the ranks of M and N. -/
@[stacks 0H9X] #check (Module.rank_tensor_of_isDomain :
  ∀ {R : Type u} [CommRing R] [IsDomain R] (M N : Type u)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N],
    Module.rank R (M ⊗[R] N) = Module.rank R M * Module.rank R N)

/- Lemma (0H9X) (2): Over a domain R, if M is finitely presented, the rank
of M →ₗ[R] N is the product of the ranks of M and N, with N arbitrary. -/
@[stacks 0H9X] #check (Module.rank_linearMap_of_finitePresentation :
  ∀ {R : Type u} [CommRing R] [IsDomain R] (M N : Type u)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M],
    Module.rank R (M →ₗ[R] N) = Module.rank R M * Module.rank R N)
