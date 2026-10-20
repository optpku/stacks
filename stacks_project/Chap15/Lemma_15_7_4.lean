/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Relative
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.7.4

Finiteness of the relative fibre-product module is recalled from the relative pullback-adjunction
API.

@stack 08IH
-/

/- Lemma 15.7.4: finite components have a finite relative fibre-product module. -/
@[stacks 08IH "Lemma 15.7.4: finite relative fibre-product module"]
#check @FiberProductBaseChangeSituation.relativeRightAdjoint_finite

end
