/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.PseudoPullback

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FiberedCategoryOver.Setoids C}
variable {F : X ⟶ Y} {G : Z ⟶ Y}
variable (P : Bicategory.PseudoPullbackCone F G)
variable (hP : P.IsBilimit)

/- Lemma 4.39.8: applying the fibrewise-isomorphism-class presheaf to a bicategorical
`2`-fibre-product cone of categories fibred in setoids gives a pullback square of presheaves. -/
@[stacks 04SD]
#check (FiberedCategoryOver.Setoids.componentsPresheaf.isPullback_of_isBilimit P hP :
  CategoryTheory.IsPullback
    (FiberedCategoryOver.Setoids.componentsMap P.fst)
    (FiberedCategoryOver.Setoids.componentsMap P.snd)
    (FiberedCategoryOver.Setoids.componentsMap F)
    (FiberedCategoryOver.Setoids.componentsMap G))

end CategoryTheory
