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
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
variable {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

/- Lemma (0H9W): Cardinal rank is additive in a short exact sequence of modules
over a domain. -/
@[stacks 0H9W] #check
  (Module.rank_eq_add_of_shortExact : ∀ (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g),
    Module.rank R N = Module.rank R M + Module.rank R P)
