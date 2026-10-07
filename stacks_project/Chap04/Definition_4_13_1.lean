module

public import Mathlib.CategoryTheory.Category.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)

/- Definition 4.13.1 (1): a morphism `f : X ⟶ Y` is a monomorphism when postcomposition by
`f` is injective, exactly as recorded by the canonical predicate `Mono f`. -/
@[stacks 003B "monomorphism by right cancellation"]
#check (Mono f : Prop)

/- Definition 4.13.1 (2): a morphism `f : X ⟶ Y` is an epimorphism when precomposition by
`f` is injective, exactly as recorded by the canonical predicate `Epi f`. -/
@[stacks 003B "epimorphism by left cancellation"]
#check (Epi f : Prop)

end CategoryTheory
