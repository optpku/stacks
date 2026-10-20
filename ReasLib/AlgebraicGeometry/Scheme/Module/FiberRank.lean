/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.FiberRank

/-!
# Fibers and fiber ranks of scheme modules

This is the scheme-level spelling of the locally-ringed-space fiber API.  The tensor-product
construction remains owned by `LocallyRingedSpace.Modules`; these abbreviations remove the
otherwise repetitive conversion through `X.toLocallyRingedSpace` in scheme applications.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The fiber of a scheme module at a point, viewed through the underlying locally ringed space. -/
abbrev fiber (ℱ : X.Modules) (x : X) : Type u :=
  LocallyRingedSpace.Modules.fiber (X := X.toLocallyRingedSpace) ℱ x

/-- The natural-valued finite rank of the fiber of a scheme module at a point. -/
noncomputable abbrev fiberFinrank (ℱ : X.Modules) (x : X) : ℕ :=
  LocallyRingedSpace.Modules.fiberFinrank (X := X.toLocallyRingedSpace) ℱ x

/-- The integer-valued fiber-rank function of a scheme module. -/
noncomputable abbrev fiberRank (ℱ : X.Modules) (x : X) : ℤ :=
  LocallyRingedSpace.Modules.fiberRank (X := X.toLocallyRingedSpace) ℱ x

/-- The condition that the fiber-rank function of a scheme module is locally constant. -/
abbrev IsFiberRankLocallyConstant (ℱ : X.Modules) : Prop :=
  LocallyRingedSpace.Modules.IsFiberRankLocallyConstant
    (X := X.toLocallyRingedSpace) ℱ

/-- The scheme-level fiber-rank condition is exactly local constancy of the named scheme
fiber-rank function. -/
theorem isFiberRankLocallyConstant_iff (ℱ : X.Modules) :
    IsFiberRankLocallyConstant ℱ ↔ IsLocallyConstant (fiberRank ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
