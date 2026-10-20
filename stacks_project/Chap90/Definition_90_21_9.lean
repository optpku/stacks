/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.Quotient
import StacksCheckRecall

universe u v w

open CategoryTheory
open scoped BasedFunctor

/- Definition 90.21.9 (1): for a groupoid in functors `G = (U, R, s, t, c)` on a
category `C`, the assignment `T ↦ (U(T), R(T), s, t, c)` is `G.toFunctor : C ⥤ Grpd`,
and the quotient category cofibered in groupoids `[U/R] ⟶ C` is
`GroupoidInFunctors.quotient G`, the category cofibered in groupoids associated to
this functor as in Remarks 90.5.2 (9). -/
@[stacks 06KB] #check (CategoryTheory.GroupoidInFunctors.quotient :
  ∀ {C : Type u} [Category.{v} C], GroupoidInFunctors.{u, v, w} C →
    CofiberedCategoryOver.Groupoids.{u, v, max u w, max v w} C)

/- Definition 90.21.9 (2): the quotient morphism `U ⟶ [U/R]` is
`GroupoidInFunctors.quotientMorphism G`, the morphism of categories cofibered in
groupoids over `C` sending `x ∈ U(T)` to the object `(T, x)` and sending
`f : T ⟶ T'` to the Grothendieck morphism `(f, id) : (T, x) ⟶ (T', U(f)(x))`
lying over `f`. -/
@[stacks 06KB] #check (CategoryTheory.GroupoidInFunctors.quotientMorphism :
  ∀ {C : Type u} [Category.{v} C] (G : GroupoidInFunctors.{u, v, w} C),
    (Functor.ofTypeValued G.U).toBasedCategory ⥤ᵇ
      (CategoryTheory.GroupoidInFunctors.quotient G).toBasedCategory)
