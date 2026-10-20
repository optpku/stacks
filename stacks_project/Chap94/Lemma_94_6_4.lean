/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {S : Scheme.{u}}
variable {X Y Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
variable {f : X ⟶ Y} {g : Z ⟶ Y}

/- Lemma 94.6.4: let `S` be a scheme and let `X`, `Y`, `Z` be categories fibred in
groupoids over `Over S`. If `f : X ⟶ Y` is a representable 1-morphism and
`g : Z ⟶ Y` is any 1-morphism, then the base-change projection
`TwoFibreProduct.fst g f : TwoFibreProduct.apex g f ⟶ Z` is a representable
1-morphism. -/
@[stacks 02ZT]
#check (CategoryTheory.Bicategory.HomProperty.twoFibreProduct_fst
    (relativelyRepresentable.homProperty (C := Over S)) g f :
    relativelyRepresentable f →
      relativelyRepresentable (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f))

end CategoryTheory.FiberedCategoryOver.Groupoids
