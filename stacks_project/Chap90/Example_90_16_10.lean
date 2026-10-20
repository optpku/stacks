/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
import StacksCheckRecall

/-!
# Prorepresentable functors are deformation functors

A prorepresentable functor on `ArtinianLocalAlgCat Λ k` is a deformation functor:
the associated cofibered set is a deformation category.
-/

@[expose] public section

open CategoryTheory CategoryOfElements

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 90.16.10: a prorepresentable functor `F : ArtinianLocalAlgCat Λ k ⥤ Type u`
is a deformation functor, in the sense that the associated cofibered set
`CategoryOfElements.π F` is a deformation category. -/
@[stacks 06JB] #check (CategoryTheory.Functor.instIsDeformationCategory_π :
  ∀ {F : ArtinianLocalAlgCat Λ k ⥤ Type u} [Functor.IsProrepresentable F],
    Functor.IsDeformationCategory (CategoryOfElements.π F))

#check (CategoryTheory.Functor.instIsPredeformationFunctor_of_isProrepresentable :
  ∀ {F : ArtinianLocalAlgCat Λ k ⥤ Type u} [Functor.IsProrepresentable F],
    Functor.IsPredeformationFunctor F)
