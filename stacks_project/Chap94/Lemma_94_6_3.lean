module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable {X Y Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
variable {f : X ⟶ Y} {g : Y ⟶ Z}
variable (hf : relativelyRepresentable f) (hg : relativelyRepresentable g)

/- Lemma 94.6.3: let `S` be a scheme and let `X`, `Y`, `Z` be categories fibred in
groupoids over `Over S`. If `f : X ⟶ Y` and `g : Y ⟶ Z` are representable
1-morphisms, then the composite `f ≫ g : X ⟶ Z` is a representable 1-morphism. -/
@[stacks 02ZS]
#check (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.comp_mem hf hg :
  relativelyRepresentable (f ≫ g))
