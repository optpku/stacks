/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Representable.Identity
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Limits.HasPullback f g]
variable (hf : Limits.HasPullbacksAlong f)

/- `MorphismProperty.pullback_snd` specializes the verified stability instance
`Functor.relativelyRepresentable.isStableUnderBaseChange` to the canonical pullback projection.
The neutral identity bridge converts the Definition 4.6.4 hypothesis to that morphism-property
presentation and converts the result back to `HasPullbacksAlong`, so the statement retains one
canonical notion of representability. -/

/- Lemma 4.6.6: if `f : x ⟶ y` is representable, then every base change `x' ⟶ y'` of `f` along
`y' ⟶ y` is representable. -/
@[stacks 001Z "representability is stable under base change"]
#check (Functor.relativelyRepresentable.hasPullbacksAlong_of_id
  (((𝟭 C).relativelyRepresentable).pullback_snd f g
    (Functor.relativelyRepresentable.id_of_hasPullbacksAlong hf)) :
  Limits.HasPullbacksAlong (Limits.pullback.snd f g))

end CategoryTheory
