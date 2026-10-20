/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
import StacksCheckRecall

universe u

/-!
# Lemma 28.16.2 compatibility entry point

The affine finite-presentation criterion for associated module sheaves is owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine`.
-/

/- Lemma 28.16.2: On `Spec R`, the module sheaf `AlgebraicGeometry.tilde M` is of finite
presentation if and only if `M` is a finitely presented `R`-module. -/
@[stacks 01PC]
#check
  (AlgebraicGeometry.Scheme.Modules.tilde_isFinitePresentation_iff_module_finitePresentation :
    ∀ {R : CommRingCat.{u}} (M : ModuleCat R),
      SheafOfModules.IsFinitePresentation (AlgebraicGeometry.tilde M) ↔
        Module.FinitePresentation R M)
