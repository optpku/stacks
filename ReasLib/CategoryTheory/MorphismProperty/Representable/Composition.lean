module

public import Mathlib.CategoryTheory.MorphismProperty.Representable

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor.relativelyRepresentable

variable {F : C ⥤ D}

/-- The composite of two relatively representable morphisms is relatively representable. -/
theorem comp_mem {X Y Z : D} (first : X ⟶ Y) (second : Y ⟶ Z)
    (hfirst : F.relativelyRepresentable first) (hsecond : F.relativelyRepresentable second) :
    F.relativelyRepresentable (first ≫ second) :=
  MorphismProperty.comp_mem F.relativelyRepresentable first second hfirst hsecond

end Functor.relativelyRepresentable

end CategoryTheory
