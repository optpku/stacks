/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PushoutQuotient
import StacksCheckRecall

/-!
# A fork-shaped colimit

@stack 00D8

Example 10.8.5 identifies the colimit of `Ma -> Mb` and `Ma -> Mc` with the cokernel of
`x |-> (mu_ab x, -mu_ac x)`. The reusable quotient model, its universal property, and its
kernel formulas are owned by `ModuleCat.PushoutQuotient`; this file retains only the
source-specific failure of the directed-system conclusion.
-/

@[expose] public section

/- Example 10.8.5: the fork gives a direct counterexample to the directed-system conclusion of
Lemma 10.8.4. -/
@[stacks 00D8 "failure without directedness"]
#check @ModuleCat.PushoutQuotient.exists_inl_eq_zero_not_eventually_zero

@[stacks 00D8 "explicit fork quotient"]
#check @ModuleCat.PushoutQuotient.quotient

@[stacks 00D8 "explicit fork colimit"]
#check @ModuleCat.PushoutQuotient.isColimit

@[stacks 00D8 "left-leg kernel formula"]
#check @ModuleCat.PushoutQuotient.ker_inl

@[stacks 00D8 "source kernel formula"]
#check @ModuleCat.PushoutQuotient.ker_inl_comp
