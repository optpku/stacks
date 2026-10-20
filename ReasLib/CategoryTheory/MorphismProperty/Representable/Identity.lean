module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative representability for the identity functor

For the identity functor, relative representability is exactly existence of
pullbacks along the given morphism.  This file exposes that change of
presentation without registering either direction as a typeclass instance.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Functor.relativelyRepresentable

/-- Relative representability with respect to the identity functor is equivalent to existence
of all pullbacks along the represented morphism. -/
@[stacks 001X]
theorem id_iff_hasPullbacksAlong {X Y : C} (f : X ⟶ Y) :
    (𝟭 C).relativelyRepresentable f ↔ HasPullbacksAlong f := sorry

/-- Existence of all pullbacks along a morphism gives its identity-relative-representability
presentation. -/
theorem id_of_hasPullbacksAlong {X Y : C} {f : X ⟶ Y}
    (hf : HasPullbacksAlong f) :
    (𝟭 C).relativelyRepresentable f := sorry

/-- Identity-relative representability of a morphism gives pullbacks along that morphism. -/
theorem hasPullbacksAlong_of_id {X Y : C} {f : X ⟶ Y}
    (hf : (𝟭 C).relativelyRepresentable f) :
    HasPullbacksAlong f := sorry

end Functor.relativelyRepresentable

end CategoryTheory
