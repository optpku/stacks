module

public import Mathlib.CategoryTheory.Category.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X : C}
variable (f : X ⟶ X) (h : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g)

/- The source's resulting notation is the canonical identity datum `CategoryStruct.id`, written
`𝟙 X`. -/
#check (𝟙 X : X ⟶ X)

/- Remark 4.2.3: a morphism out of `X` acting as a left identity on all maps with source `X`
is the canonical identity `𝟙 X`; applying this to each candidate gives the textbook uniqueness
statement. This is the canonical owner lemma `id_of_comp_left_id`. -/
@[stacks 0016]
#check (id_of_comp_left_id f h : f = 𝟙 X)

/- Companion recall: a morphism into `X` acting as a right identity on all maps with target `X`
is the canonical identity `𝟙 X`; this is the owner lemma `id_of_comp_right_id`. -/
@[stacks 0016 "uniqueness of the identity from the right-unit law"]
#check id_of_comp_right_id

end CategoryTheory
