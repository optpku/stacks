module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.TargetYoneda
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/- Lemma 96.5.2: Let `f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf`. The following are equivalent: `f` is representable, and for
every object `y` of `Y` the functor `Xᵒᵖ ⥤ Type`, `x ↦ (toFunctor f).obj x ⟶ y`,
is representable. -/
@[stacks 06W7] #check (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.iff_targetYoneda f :
    relativelyRepresentable f ↔ targetYoneda.representable f)
