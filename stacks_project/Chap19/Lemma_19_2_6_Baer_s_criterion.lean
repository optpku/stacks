/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.Baer
import StacksCheckRecall

@[expose] public section

universe u

variable {R : Type u} [Ring R]
variable {Q : Type u} [AddCommGroup Q] [Module R Q]

/- Lemma 19.2.6 (Baer's criterion): for a ring `R` and an `R`-module `Q`, the module `Q` is
injective if and only if every `R`-linear map from an ideal `I : Ideal R` to `Q` extends along the
inclusion `I → R`. This is `Module.Injective.iff_baer`, because
`Module.Baer R Q` is exactly the extension property for all ideals of `R`. -/
@[stacks 05NU] #check
  (Module.Injective.iff_baer (R := R) (Q := Q) :
    Module.Injective R Q ↔ Module.Baer R Q)
