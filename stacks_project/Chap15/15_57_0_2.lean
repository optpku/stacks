/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.BoundedAbove
import StacksCheckRecall

@[expose] public section

/-!
# 15.57.0.2: bounded-above derived extension of scalars

@stack 064H
-/

/- 15.57.0.2 (064H): extension of scalars admits a bounded-above left derived functor. -/
@[stacks 064H "bounded-above derived extension-of-scalars existence"]
#check @ModuleCat.BoundedAbove.extendScalars_hasLeftDerived
