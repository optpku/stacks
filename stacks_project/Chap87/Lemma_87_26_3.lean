/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Mono

@[expose] public section

open CategoryTheory Limits

universe u v

/- Lemma 87.26.3: a base change of a monomorphism is a monomorphism
(such monomorphisms being categorical `Mono` as in 87.26.1). -/
@[stacks 0GHU] #check
  (CategoryTheory.Mono.pullbackSnd :
    ∀ {C : Type u} [CategoryTheory.Category.{v} C] {X Y Z : C}
      (f : X ⟶ Z) (g : Y ⟶ Z)
      [CategoryTheory.Limits.HasPullback f g] [CategoryTheory.Mono f],
      CategoryTheory.Mono (CategoryTheory.Limits.pullback.snd f g))
