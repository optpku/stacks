module

public import Mathlib.CategoryTheory.MorphismProperty.Representable

@[expose] public section

namespace CategoryTheory

open Limits MorphismProperty

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor.relativelyRepresentable

variable {F : C ⥤ D}

/-- Relative representability is preserved by pulling back a relatively representable morphism. -/
theorem pullback_fst {X Y S : D} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    (hg : F.relativelyRepresentable g) :
    F.relativelyRepresentable (pullback.fst f g) := sorry

end Functor.relativelyRepresentable

end CategoryTheory
