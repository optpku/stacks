module

public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

universe u v

namespace CategoryTheory.Mono

/-- The composition of two monomorphisms is a monomorphism. -/
theorem comp {C : Type u} [Category.{v} C] {X Y Z : C}
    (first : X ⟶ Y) (second : Y ⟶ Z) [Mono first] [Mono second] :
    Mono (first ≫ second) := CategoryTheory.mono_comp first second

end CategoryTheory.Mono
