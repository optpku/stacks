/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Hom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.12.10 -- Inverse-image/direct-image Hom functor

The source statement is owned by the neutral heterogeneous API
`CategoryTheory.CartesianBasedFunctor.PushforwardHom.functor`. Its construction composes the
stackification universal property with the canonical pushforward-pullback Hom functor; the
bundled `StackOver.InverseImage.homFunctor` is an application-facing companion.
-/

namespace CategoryTheory

/- The deterministic data owner sends morphisms out of a chosen inverse-image stack to
morphisms from the original stack into the pulled-back target stack. -/
#check @StackOver.InverseImage.homFunctor
#check @StackOver.InverseImage.homFunctor.obj.toMor
#check @StackOver.InverseImage.homFunctor.obj.toBasedFunctor
#check @StackOver.InverseImage.homFunctor.obj.toFunctor
#check @StackOver.InverseImage.homFunctor.obj.fiberFunctor
#check @StackOver.InverseImage.homFunctor.map.toMor₂
#check @StackOver.InverseImage.homFunctor.map.toBasedNatTrans
#check @StackOver.InverseImage.homFunctor.map.toNatTrans
#check @StackOver.InverseImage.homFunctor.map.app

/- Before bundling an inverse-image stack, the same construction is available for independent
total-category universes as a composite of the two canonical cartesian Hom functors. -/
#check @CartesianBasedFunctor.PushforwardHom.functor
#check @CartesianBasedFunctor.PushforwardHom.functor.obj
#check @CartesianBasedFunctor.PushforwardHom.functor.map

/- Lemma 8.12.10 (04WK): the canonical inverse-image/direct-image Hom functor is an
equivalence of morphism categories. -/
@[stacks 04WK]
#check @StackOver.InverseImage.homFunctor.isEquivalence

#check @CartesianBasedFunctor.PushforwardHom.functor.isEquivalence

end CategoryTheory
