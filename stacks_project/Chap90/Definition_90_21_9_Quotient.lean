/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.Quotient

universe u v w

open CategoryTheory
open scoped BasedFunctor

#check (CategoryTheory.GroupoidInFunctors.quotientMorphism :
  ∀ {C : Type u} [Category.{v} C] (G : GroupoidInFunctors.{u, v, w} C),
    (Functor.ofTypeValued G.U).toBasedCategory ⥤ᵇ
      (CategoryTheory.GroupoidInFunctors.quotient G).toBasedCategory)
