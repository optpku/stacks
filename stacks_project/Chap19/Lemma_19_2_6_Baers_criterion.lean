/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Injective
import StacksCheckRecall

@[expose] public section

universe u

variable {R : Type u} [Ring R]
variable {Q : Type u} [AddCommGroup Q] [Module R Q]

/- Lemma 19.2.6 (Baer's criterion): for a ring `R` and an `R`-module `Q`, the module `Q` is
injective if and only if every `R`-linear map from an ideal `I : Ideal R` to `Q` extends along the
inclusion `I → R`. This is the canonical mathlib theorem `Module.Baer.iff_injective`, because
`Module.Baer R Q` is exactly the extension property for all ideals of `R`. -/
@[stacks 05NU] #check
  (Module.Baer.iff_injective (R := R) (Q := Q) :
    Module.Baer R Q ↔ Module.Injective R Q)
