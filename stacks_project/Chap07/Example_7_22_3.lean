/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

/-!
# Example 7.22.3

The topology-comparison direct-image isomorphism is the identity-adjunction specialization of
the generic continuous-right-adjoint comparison.
-/

@[expose] public section

/- Example 7.22.3 (0EWJ): for `J' ≤ J`, the direct image of the topology-comparison morphism
is the identity-adjunction specialization of the continuous-right-adjoint direct-image comparison. -/
@[stacks 0EWJ] #check @CategoryTheory.Functor.ContinuousRightAdjoint.pushforwardContinuousIso
