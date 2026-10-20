/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor.Right
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic

/-!
# Derived tensor products of modules on schemes

This module supplies the fixed-right derived tensor instance for module sheaves on a scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Fixed-right derived tensor products exist for module sheaves on a scheme. -/
noncomputable instance hasDerivedTensorRight (X : Scheme.{u}) :
    @DerivedCategory.DerivedTensor.Right.Has
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ := sorry

end AlgebraicGeometry.Scheme.Modules
