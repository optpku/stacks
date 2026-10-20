/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.HomEquivalence

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.9: the forward functor of the completion–restriction hom-category equivalence. -/
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.homEquivFunctor :
  ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)),
    ((restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) ⥤
      (G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)))
