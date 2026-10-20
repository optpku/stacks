/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Colimits
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.42.5

Finite connected colimit preservation belongs to the reusable
almost-cocontinuity API rather than to the proof infrastructure of this
chapter.
-/

@[expose] public section

/- Lemma 7.42.5 (04B9): continuous pushforward along an almost cocontinuous
functor preserves finite connected colimits of type-valued sheaves. -/
@[stacks 04B9] #check @CategoryTheory.Functor.IsAlmostCocontinuous.pushforwardContinuous_preservesFiniteConnectedColimits

/- The aggregate preservation instance supplies every finite connected shape through the
canonical class projection. -/
#check @CategoryTheory.Limits.PreservesFiniteConnectedColimits.preservesColimitsOfShape
