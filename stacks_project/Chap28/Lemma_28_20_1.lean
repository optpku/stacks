/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 28.20.1 compatibility entry point

The affine local-freeness and finite-local-freeness criteria are owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine`.
-/

open AlgebraicGeometry

universe u

/- Lemma 28.20.1: the module sheaf associated to `M` on `Spec R` is locally free exactly
when `M` is locally free. -/
@[stacks 05JM]
#check (AlgebraicGeometry.Scheme.Modules.tilde_isLocallyFree_iff_module_locallyFree :
  ∀ {R : CommRingCat.{u}} (M : ModuleCat R),
    SheafOfModules.IsLocallyFree
      (J := Opens.grothendieckTopology (Spec R).toRingedSpace)
      (R := (Spec R).toRingedSpace.ringCatSheaf)
      (AlgebraicGeometry.tilde M) ↔
        Module.LocallyFree R M)

#check (AlgebraicGeometry.Scheme.Modules.tilde_isFiniteLocallyFree_iff_module_finiteLocallyFree :
  ∀ {R : CommRingCat.{u}} (M : ModuleCat R),
    SheafOfModules.IsFiniteLocallyFree (AlgebraicGeometry.tilde M) ↔
      Module.FiniteLocallyFree R M)
