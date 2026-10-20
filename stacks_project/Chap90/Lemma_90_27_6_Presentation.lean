/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.AssociatedMorphism

open CategoryTheory CompleteLocalAlgCat
open CofiberedCategoryOver.Groupoids

universe u

/- The associated morphism of a formal object has its actual restricted coyoneda
as source and the original category cofibered in groupoids as target. -/
#check (FormalObject.associatedMorphismOver :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {G : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)}
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)),
    Functor.ofTypeValued.{u + 1, u, u} (restrictedCoyoneda ξ.base) ⟶ G)

/- A formal object's associated morphism determines a kernel-pair groupoid in functors. -/
#check (CategoryTheory.GroupoidInFunctors.ofFormalObject :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {G : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)}
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)),
    GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
