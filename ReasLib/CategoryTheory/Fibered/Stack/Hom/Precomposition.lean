module

public import ReasLib.CategoryTheory.Fibered.Stack.Hom
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Precomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Precomposition from stack morphisms to ambient fibred-category morphisms

For a morphism `i : X ⟶ Y` into a bundled stack, this module packages
precomposition on morphisms from `Y` to another bundled stack.  Its codomain is
the ambient Hom category from `X`; this is the natural generality because `X`
need not itself be a stack.

## Main declarations

* `CategoryTheory.StackOver.Hom.precomp` -- the stack-to-ambient precomposition functor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Precompose a morphism of stacks by an ambient morphism of fibred categories.  The target
is the ambient Hom category because the source `X` need not carry a stack structure. -/
@[stacks 04W9 "precomposition from stack morphisms to ambient morphisms"]
noncomputable abbrev precomp
    (Z : StackOver.{u, v, w, vS} J) {X : FiberedCategoryOver.{u, v, w, vS} C}
    {Y : StackOver.{u, v, w, vS} J} (i : X ⟶ Y.toFiberedCategoryOver) :
    (Y ⟶ Z) ⥤ (X ⟶ Z.toFiberedCategoryOver) :=
  Bicategory.InducedBicategory.precompToAmbient Z i

end StackOver.Hom

end CategoryTheory
