module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.TargetYoneda

@[expose] public section

open CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u v

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.iff_targetYoneda :
    ∀ (F : X ⟶ Y), relativelyRepresentable F ↔ targetYoneda.representable F)
