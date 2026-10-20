/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.TopCohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

export CategoryTheory.DerivedCategory.Bounded (topCohomologyMap topCohomologyMap_def)

/- The degree-`b` cohomology map induced by a morphism from a bounded single object. -/
#check (CategoryTheory.DerivedCategory.Bounded.topCohomologyMap :
    ∀ {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (b : ℤ) {N : C} (X : DerivedCategory.Bounded C)
    (f : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X),
    N ⟶ (DerivedCategory.Bounded.homologyFunctor C b).obj X)

/- The defining formula for the induced top-cohomology map. -/
#check (CategoryTheory.DerivedCategory.Bounded.topCohomologyMap_def :
    ∀ {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (b : ℤ) {N : C} (X : DerivedCategory.Bounded C)
    (f : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X),
    topCohomologyMap b X f =
      (DerivedCategory.Bounded.singleFunctor.compHomologyIso C b).inv.app N ≫
        (DerivedCategory.Bounded.homologyFunctor C b).map f)
