/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Determinant
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinant sheaves on schemes

This leaf is the scheme-facing facade for the intrinsic determinant on the underlying ringed
space.  The determinant uses the canonical closed structure from the ringed-space API, while this
file exposes the consequences of finite local freeness through the global instance chain.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Determinant

variable {X : Scheme.{u}}

/-- The determinant of a finite locally free scheme module is tensor-invertible. -/
@[stacks 0FJN "finite locally free scheme module", instance]
theorem isInvertible (F : X.Modules) [SheafOfModules.IsFiniteLocallyFree F] :
    isInvertibleObject (RingedSpace.Determinant.sheaf F) := sorry

/-- The determinant of a finite locally free scheme module is finite locally free of rank one. -/
@[stacks 0FJN "rank-one determinant on a scheme", instance]
theorem rankOne (F : X.Modules) [SheafOfModules.IsFiniteLocallyFree F] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1
      (RingedSpace.Determinant.sheaf F) := sorry

section

variable (F : X.Modules) (n : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank n F]

end

end AlgebraicGeometry.Scheme.Modules.Determinant
