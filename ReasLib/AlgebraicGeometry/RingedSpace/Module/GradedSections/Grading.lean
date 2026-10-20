/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DirectSum.InternalGrading
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections

/-!
# The natural grading of a tensor-power section ring

The degreewise global sections of the tensor powers of a module form an external direct sum.
This leaf exposes its canonical internal homogeneous subgroups for projective constructions.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.GradedSections

variable {X : RingedSpace.{u}}

/-- The natural internal degree-`n` subgroup of the tensor-power section ring of `L`. -/
abbrev grading (L : X.Modules) (n : ℕ) : AddSubgroup (ring L) :=
  DirectSum.InternalGrading.summand (degree L) n

end AlgebraicGeometry.RingedSpace.GradedSections
