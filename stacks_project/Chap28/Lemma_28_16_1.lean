/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Lemma 28.16.1 compatibility entry point

The affine finite-type criterion for associated module sheaves is owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine`.
-/

/- Lemma 28.16.1: For an affine scheme `Spec R`, the associated sheaf `AlgebraicGeometry.tilde M`
is of finite type if and only if `M` is a finite `R`-module. -/
@[stacks 01PB]
#check (AlgebraicGeometry.Scheme.Modules.tilde_isFiniteType_iff_module_finite :
  ∀ {R : CommRingCat.{u}} (M : ModuleCat R),
    SheafOfModules.IsFiniteType (AlgebraicGeometry.tilde M) ↔ Module.Finite R M)
