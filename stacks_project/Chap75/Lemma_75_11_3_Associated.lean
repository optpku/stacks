/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.Lemma_69_16_2_Tensor

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Associated

/-! # Compatibility checks for associated quasi-coherent modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.tensorOXMap :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    {M N : ModuleCat.{u} (globalSectionsRing X)} (f : M ⟶ N),
    AlgebraicGeometry.AlgebraicSpace.tensorOX X M ⟶
      AlgebraicGeometry.AlgebraicSpace.tensorOX X N)

#check (AlgebraicGeometry.AlgebraicSpace.tensorOXFunctor :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ModuleCat.{u} (globalSectionsRing X) ⥤ X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.tensorOXFunctor_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (M : ModuleCat.{u} (globalSectionsRing X)),
    (tensorOXFunctor X).obj M = AlgebraicGeometry.AlgebraicSpace.tensorOX X M)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.tensorOX :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ModuleCat.{u} (globalSectionsRing X) ⥤ QCoh X)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.tensorOX_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (M : ModuleCat.{u} (globalSectionsRing X)),
    ((QCoh.tensorOX X).obj M).obj = (tensorOXFunctor X).obj M)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.tensorOX.additive :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X], (QCoh.tensorOX X).Additive)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.tensorOX.preservesFiniteLimits :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X],
    PreservesFiniteLimits (QCoh.tensorOX X))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.tensorOX.preservesFiniteColimits :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X],
    PreservesFiniteColimits (QCoh.tensorOX X))

end AlgebraicGeometry.AlgebraicSpace
