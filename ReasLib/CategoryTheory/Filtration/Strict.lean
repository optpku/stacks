module

public import ReasLib.CategoryTheory.Filtration.Category
public import ReasLib.CategoryTheory.Filtration.ImageSubobject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Morphisms of Filtered Objects

A morphism of filtered objects is strict when the image of each filtration stage equals the
intersection of the total image with the corresponding target stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]
variable {A B : FilteredObject C}

/-- A morphism of filtered objects is strict when, for every integer `i`, the image of the `i`-th
filtration step is exactly the intersection of the total image with the `i`-th filtration step
of the target. -/
@[stacks 0123]
def Strict (f : A ⟶ B) : Prop :=
  ∀ i : ℤ, imageSubobject ((A.filtration i).arrow ≫ f.hom) =
    imageSubobject f.hom ⊓ B.filtration i

/-- Strictness is equivalently the statement that the quotient filtration of the source agrees
with the intersection of the total image and the target filtration at every stage. -/
theorem strict_iff_quotient_eq_inf (f : A ⟶ B) :
    Strict f ↔ ∀ i : ℤ, A.filtration.quotient f.hom i =
      imageSubobject f.hom ⊓ B.filtration i := sorry

/-- The identity morphism of a filtered object is strict. -/
@[simp] theorem strict_id (A : FilteredObject C) : Strict (𝟙 A) := sorry

end CategoryTheory.FilteredObject.Hom
