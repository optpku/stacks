/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Cohen-Macaulay modules on regular schemes

This file relates Cohen-Macaulay coherent modules of full support to finite locally free modules
on regular schemes.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [Scheme.Regular X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- A coherent module of full support on a regular scheme is Cohen-Macaulay exactly when it is
finite locally free. -/
theorem cohenMacaulay_iff_isFiniteLocallyFree_of_regular_of_support_eq_univ
    (hsupp : RingedSpace.moduleSupport ℱ = Set.univ) :
    CohenMacaulay ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := sorry

namespace CohenMacaulay

/-- For a coherent module on a regular scheme, Cohen-Macaulayness with full support is equivalent
to finite local freeness with full support. -/
theorem and_fullSupport_iff_isFiniteLocallyFree_and_fullSupport :
    (CohenMacaulay ℱ ∧ RingedSpace.moduleSupport ℱ = Set.univ) ↔
      (SheafOfModules.IsFiniteLocallyFree ℱ ∧ RingedSpace.moduleSupport ℱ = Set.univ) := sorry

end CohenMacaulay

end AlgebraicGeometry.Scheme.Modules
