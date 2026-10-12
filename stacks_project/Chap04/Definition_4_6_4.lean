/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Representable.Identity
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)

/-
The source-facing need is the predicate on `f : x ⟶ y` requiring a pullback against every
`g : z ⟶ y`. The canonical quantified-existence owner is `HasPullbacksAlong f`; the equivalent
identity-functor presentation is exposed by
`Functor.relativelyRepresentable.id_iff_hasPullbacksAlong`.
-/

/- Definition 4.6.4: a morphism `f : x ⟶ y` is representable when the fibre product of `f`
with every morphism `g : z ⟶ y` exists; this is exactly `HasPullbacksAlong f`. -/
@[stacks 001X "pullbacks exist along a fixed morphism"]
#check (HasPullbacksAlong f : Prop)

/- The identity-relative-representability presentation is available without introducing a
second notion of representable morphism. -/
#check (Functor.relativelyRepresentable.id_iff_hasPullbacksAlong f)

end CategoryTheory.Limits
