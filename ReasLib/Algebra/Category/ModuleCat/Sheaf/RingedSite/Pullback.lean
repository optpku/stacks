/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocalGeneration
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent

/-!
# Pullback Properties of Module Sheaves

Convenience import for the property-specific inverse-image preservation leaves.  These
statements hold for arbitrary `RingCat` sheaves and live in namespace `SheafOfModules`
under `Sheaf/PullbackContinuous/`.
For functor computation and naturality, use Mathlib's
`SheafOfModules.pullbackId`, `SheafOfModules.pullbackComp`, and
`SheafOfModules.pullback_assoc` directly.
-/
