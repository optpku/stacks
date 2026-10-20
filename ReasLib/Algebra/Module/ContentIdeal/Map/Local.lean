/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.ContentIdeal.Finite
public import ReasLib.Algebra.Module.ContentIdeal.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Content ideals and closed fibers over local rings

@stack 0ASC
-/

universe u v w

namespace IsContentIdeal

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Flat A N]
variable {x : M} {I : Ideal A}

open IsLocalRing

/-- Lemma 15.24.3, tag `0ASC`: over a local ring, a map of flat modules
preserves a content ideal when its reduction modulo the maximal ideal is
injective. No finiteness assumption on the source module is required. -/
@[stacks 0ASC "content ideals and injectivity on the closed fiber"]
theorem map_of_injective_mod_maximalIdeal (hI : IsContentIdeal x I)
    (f : M →ₗ[A] N)
    (hf : Function.Injective
      (f.quotientMapByIdeal (maximalIdeal A))) :
    IsContentIdeal (f x) I := sorry
-- Proof strategy: use `hI.fg` to reduce every competing ideal inside `I` to a finite quotient,
-- apply Nakayama to a nonzero quotient of `I`, and use flatness to identify the tensor kernels;
-- `hf` rules out a smaller ideal, while membership follows by mapping `hI.mem`.

end IsContentIdeal
