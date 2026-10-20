module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Slice
import StacksCheckRecall

/-!
# Morphisms of schemes induce representable 1-morphisms of slice fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

section

variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)

/- Lemma 94.6.1: a morphism `f : X ⟶ Y` of schemes over `S` induces a relatively
representable 1-morphism `overMap f` between the corresponding slice fibrations. -/
@[stacks 02ZR] #check
  (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.overMap
    (C := Over S) (X := X) (Y := Y) f :
      CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable
        (CategoryTheory.FiberedCategoryOver.Groupoids.overMap f))

end
