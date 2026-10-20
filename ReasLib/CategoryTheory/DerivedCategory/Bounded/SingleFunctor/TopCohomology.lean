/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Homology

@[expose] public section

universe w v u

namespace CategoryTheory.DerivedCategory.Bounded

/-- The map on degree-`b` cohomology induced by a morphism from the bounded
single object concentrated in degree `b`, with its source identified with `N`. -/
noncomputable def topCohomologyMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (b : ℤ) {N : C} (X : DerivedCategory.Bounded C)
    (f : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X) :
    N ⟶ (DerivedCategory.Bounded.homologyFunctor C b).obj X :=
  (DerivedCategory.Bounded.singleFunctor.compHomologyIso C b).inv.app N ≫
    (DerivedCategory.Bounded.homologyFunctor C b).map f

/-- The induced top-cohomology map is the inverse single-object cohomology
identification followed by the map of the cohomology functor. -/
theorem topCohomologyMap_def
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (b : ℤ) {N : C} (X : DerivedCategory.Bounded C)
    (f : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X) :
    topCohomologyMap b X f =
      (DerivedCategory.Bounded.singleFunctor.compHomologyIso C b).inv.app N ≫
        (DerivedCategory.Bounded.homologyFunctor C b).map f := sorry

end CategoryTheory.DerivedCategory.Bounded
