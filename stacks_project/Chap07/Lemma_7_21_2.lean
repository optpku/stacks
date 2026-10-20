/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

-- Comparison isomorphisms for composite cocontinuous site functors live in ReasLib.
public import ReasLib.CategoryTheory.Sites.Topos.Composition
import StacksCheckRecall

@[expose] public section

/- Lemma 7.21.2 (03L5): cocontinuous site functors compose, and the direct image of the induced
composite morphism of topoi is canonically isomorphic to the composite direct image. The generic
comparison API is independent of the textbook chapter. -/
#check @CategoryTheory.isCocontinuous_comp
#check @CategoryTheory.Functor.sheafPushforwardCocontinuousIso
#check @CategoryTheory.Functor.sheafPushforwardCocontinuousComp'
#check @CategoryTheory.Functor.sheafPullbackComp'

@[stacks 03L5] #check @CategoryTheory.Functor.sheafPushforwardCocontinuousComp
