/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Tensor
public import stacks_project.Chap75.Lemma_75_5_6_Instances

/-!
# Derived tensor of quasi-coherent complexes on algebraic spaces

Fixed-right derived tensor preserves the full subcategory of `D(𝒪_X)` on complexes whose
cohomology sheaves are quasi-coherent, so `D_QCoh(𝒪_X)` is closed under `- ⊗^L -`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

#check (tensorRight.mapsTo : ∀ {X : AlgebraicSpace S} (L : DerivedQCoh X),
  derivedQuasiCoherentModuleProperty X ≤
    (derivedQuasiCoherentModuleProperty X).inverseImage (DerivedTensor.Right.functor L.obj))

#check (tensorRight : ∀ {X : AlgebraicSpace S} (L : DerivedQCoh X),
  DerivedQCoh X ⥤ DerivedQCoh X)

#check (tensorRight.inclusionIso : ∀ {X : AlgebraicSpace S} (L : DerivedQCoh X),
  tensorRight L ⋙ (derivedQuasiCoherentModuleProperty X).ι ≅
    (derivedQuasiCoherentModuleProperty X).ι ⋙ DerivedTensor.Right.functor L.obj)

#check (tensorObj : ∀ {X : AlgebraicSpace S} (K L : DerivedQCoh X), DerivedQCoh X)

#check (tensorObj_obj : ∀ {X : AlgebraicSpace S} (K L : DerivedQCoh X),
  (tensorObj K L).obj = (DerivedTensor.Right.functor L.obj).obj K.obj)

#check (tensor_mem : ∀ {X : AlgebraicSpace S} (K L : DerivedQCoh X),
  derivedQuasiCoherentModuleProperty X ((DerivedTensor.Right.functor L.obj).obj K.obj))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
