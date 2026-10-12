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
# 15.57.0.1: bounded-above tensor with a fixed module

@stack 064G
-/

/- 15.57.0.1 (064G): fixed-factor tensoring admits a bounded-above left derived functor. -/
@[stacks 064G "bounded-above fixed-factor derived tensor existence"]
#check @ModuleCat.BoundedAbove.tensorRight_hasLeftDerived
