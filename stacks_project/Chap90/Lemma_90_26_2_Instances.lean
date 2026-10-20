/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.KernelPair

/-!
# Predeformation and Schlessinger instances

Typed checks expose the shared inference API for deformation functors and their
kernel pairs.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

section
variable {G : ArtinianLocalAlgCat Λ k ⥤ Type w} [IsPredeformationFunctor G]

#check (CategoryTheory.Functor.instIsPredeformationCategory_ofTypeValued (G := G) :
  IsPredeformationCategory (CategoryOfElements.π G))
end

section
variable {G : ArtinianLocalAlgCat Λ k ⥤ Type w} [IsDeformationFunctor G]

#check (CategoryTheory.Functor.instHasSchlessingerH2_of_isDeformationFunctor (G := G) :
  HasSchlessingerH2 G)
end

variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}
variable (f : Functor.ofTypeValued U ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationFunctor U]

#check (CategoryTheory.GroupoidInFunctors.instIsDeformationFunctor_relation f :
  IsDeformationFunctor (GroupoidInFunctors.relation f))

#check (CategoryTheory.Functor.IsPredeformationFunctor.unique_residue
    (F := GroupoidInFunctors.relation f) :
  Nonempty (Unique ((GroupoidInFunctors.relation f).obj (residue Λ k))))
