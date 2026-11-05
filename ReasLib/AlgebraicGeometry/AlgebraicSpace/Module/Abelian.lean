/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallSheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # The abelian category of modules on an algebraic space

The original coefficient universe is retained. Actual small-atlas sheafification supplies the
native sheaf-of-modules adjunction; Mathlib constructs its finite products, kernels and cokernels.
The module category uses that complete native Abelian structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The specified atlas-site sheafification is left exact. -/
instance modulesSheafification_preservesFiniteLimits {S : Scheme.{u}} (X : AlgebraicSpace S) :
    PreservesFiniteLimits (PullbackFactory.AdditiveSheafification.sheafify
      (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)) :=
  PullbackFactory.AdditiveSheafification.sheafify_preservesFiniteLimits
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

/-- Strong sheafification uses the same actual small-atlas adjunction as the module data. -/
instance modulesHasSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
  HasSheafify.mk' (smallEtaleTopology X) AddCommGrpCat.{u}
    (PullbackFactory.AdditiveSheafification.adjunction
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X))

/-- The locally bijective characterization transports along the displayed atlas inclusion. -/
instance modulesWEqualsLocallyBijective {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  PullbackFactory.AdditiveSheafification.additiveW
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

/-- Module sheaves carry the native abelian structure from their actual sheafification
adjunction, including its constructed finite products, kernels and cokernels. -/
instance modulesAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Abelian X.Modules :=
  SheafOfModules.instAbelian (structureSheaf X)

end AlgebraicGeometry.AlgebraicSpace
