/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- The fixed-right derived tensor instance is provided by its shared mathematical owner. -/
#check (hasDerivedTensorRight :
  ∀ X : Scheme.{u}, DerivedCategory.DerivedTensor.Right.Has
    (C := RingedSpace.Modules X.toRingedSpace))

end AlgebraicGeometry.Scheme.Modules

/- The standard derived category for ringed-space quasicoherent modules is provided by its
shared mathematical owner. -/
#check
  (AlgebraicGeometry.Scheme.QCoh.Derived.ringedSpaceHasDerivedCategory :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      HasDerivedCategory
        (AlgebraicGeometry.RingedSpace.QCoh X.toRingedSpace))
