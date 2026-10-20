/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero

/-!
# Tangent-space module structure and tensor comparison

Schlessinger's condition (H2) gives a vector-space structure on the tangent value
and a natural linear comparison with evaluation on finite square-zero extensions.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [CategoryTheory.Functor.IsPredeformationCategory p]
  [CategoryTheory.Functor.HasSchlessingerH2 (CategoryTheory.Functor.fiberIsoClassFunctor p)]
variable (V : FGModuleCat.{u} k)

#check (CategoryTheory.Functor.instModule_fiberDualTangent p :
  Module k ((CategoryTheory.Functor.fiberIsoClassFunctor p).obj (dualNumber Λ k)))

#check (CategoryTheory.Functor.fiberDualTangentTensor p V :
  (CategoryTheory.Functor.fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] V →ₗ[k]
    (CategoryTheory.Functor.fiberIsoClassFunctor p).obj (squareZero Λ k V))

#check (CategoryTheory.Functor.fiberDualTangentTensor_naturality p V :
  ∀ {W : FGModuleCat.{u} k} (map : V ⟶ W)
    (value : (CategoryTheory.Functor.fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] V),
    (CategoryTheory.Functor.fiberIsoClassFunctor p).map ((squareZeroFunctor Λ k).map map)
      (CategoryTheory.Functor.fiberDualTangentTensor p V value) =
    CategoryTheory.Functor.fiberDualTangentTensor p W
      (TensorProduct.map LinearMap.id map.hom.hom value))
