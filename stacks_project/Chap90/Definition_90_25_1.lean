/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Presentation
import StacksCheckRecall

/-!
# Presentations of categories cofibered in groupoids

A presentation of a category cofibered in groupoids F by a groupoid in functors
(U, R, s, t, c) is an equivalence φ : [U/R] ⟶ F of categories cofibered in groupoids
over C.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory BasedFunctor

universe u v w

variable {C : Type u} [Category.{v} C]

/- Definition 90.25.1: a presentation of a category cofibered in groupoids `F` by a
groupoid in functors `G = (U, R, s, t, c)` is an equivalence `φ : G.quotient ⟶ F` of
categories cofibered in groupoids over `C`. -/
@[stacks 06KX] #check (CategoryTheory.GroupoidInFunctors.IsPresentation :
  (G : GroupoidInFunctors.{u, v, w} C) →
    (F : CofiberedCategoryOver.Groupoids C) → (G.quotient ⟶ F) → Prop)
