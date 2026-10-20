/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.14.2

The reusable owner is the `PreservesInjectiveObjects` instance for module direct image along a
flat morphism. Its objectwise companion states the textbook result without exposing site-level
constructions of the pullback-pushforward adjunction.
-/

/- Lemma 21.14.2 (0730): direct image along a flat morphism sends injective module sheaves to
injective module sheaves. -/
@[stacks 0730]
#check @RingedSite.Hom.modulePushforward.injective_obj_of_isFlat

#check @RingedSite.Hom.modulePushforward.preservesInjectiveObjects_of_isFlat
