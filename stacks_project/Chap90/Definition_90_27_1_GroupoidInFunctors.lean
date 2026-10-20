/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (U R : ArtinianLocalAlgCat Λ k ⥤ Type u)
  [CategoryTheory.GroupoidInFunctors.IsProrepresentableFunctors U R]

/- Definition 90.27.1: prorepresentability of the object and arrow functors. -/
#check (CategoryTheory.GroupoidInFunctors.isProrepresentableFunctors_U U R :
  Functor.IsProrepresentable U)
#check (CategoryTheory.GroupoidInFunctors.isProrepresentableFunctors_R U R :
  Functor.IsProrepresentable R)
#check (CategoryTheory.GroupoidInFunctors.isProrepresentable_iff :
  ∀ G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k),
    CategoryTheory.GroupoidInFunctors.IsProrepresentable G ↔
      Functor.IsProrepresentable G.U ∧ Functor.IsProrepresentable G.R)
#check (CategoryTheory.GroupoidInFunctors.sourceBasedFunctor :
  ∀ G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k),
    BasedCategory.ofFunctor (CategoryOfElements.π G.R) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π G.U))
#check (CategoryTheory.GroupoidInFunctors.targetBasedFunctor :
  ∀ G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k),
    BasedCategory.ofFunctor (CategoryOfElements.π G.R) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π G.U))
