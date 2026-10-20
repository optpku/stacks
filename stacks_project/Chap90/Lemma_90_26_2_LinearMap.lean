/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.KernelPair

/-!
# Dual-number algebra and kernel-pair tangent maps

Typed checks expose the shared dual-number vector space and the canonical maps
from infinitesimal automorphisms to the kernel-pair tangent sequence.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

section
variable (G : ArtinianLocalAlgCat Λ k ⥤ Type w)

#check (CategoryTheory.Functor.objDualNumberEquivSquareZero G :
  G.obj (dualNumber Λ k) ≃ G.obj (squareZero Λ k k))

variable [IsPredeformationFunctor G] [HasSchlessingerH2 G]

#check (CategoryTheory.Functor.instAddCommGroup_obj_dualNumber (G := G) :
  AddCommGroup (G.obj (dualNumber Λ k)))

#check (CategoryTheory.Functor.instModule_obj_dualNumber (G := G) :
  Module k (G.obj (dualNumber Λ k)))

#check (CategoryTheory.Functor.instAddCommGroup_tangentSpace (G := G) :
  AddCommGroup (IsPredeformationFunctor.tangentSpace G))

#check (CategoryTheory.Functor.instModule_tangentSpace (G := G) :
  Module k (IsPredeformationFunctor.tangentSpace G))
end

variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}
variable (f : Functor.ofTypeValued U ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationFunctor U]

#check (CategoryTheory.GroupoidInFunctors.connectingLinearMap f :
  infinitesimalAutomorphisms F.p →ₗ[k]
    IsPredeformationFunctor.tangentSpace (GroupoidInFunctors.relation f))

#check (CategoryTheory.GroupoidInFunctors.tangentProdLinearMap f :
  IsPredeformationFunctor.tangentSpace (GroupoidInFunctors.relation f) →ₗ[k]
    IsPredeformationFunctor.tangentSpace U × IsPredeformationFunctor.tangentSpace U)
