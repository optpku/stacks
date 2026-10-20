/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable
    {S : Scheme.{u}}
    {X' X Y' Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X' ≌ X) (eY : Y' ≌ Y) (η : eX.hom ≫ f ≅ f' ≫ eY.hom)

/- Lemma 94.6.2: in a 2-commutative square of categories fibred in groupoids over
`Over S`, equivalences on the horizontal sides preserve and reflect representability
of the vertical morphisms. -/
@[stacks 0456] #check
  (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.iff_of_equivalence
    eX eY η : relativelyRepresentable f ↔ relativelyRepresentable f')

end CategoryTheory.FiberedCategoryOver.Groupoids
