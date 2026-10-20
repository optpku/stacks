/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# The fpqc sheaf property for flatness in dimensions

This module records fpqc descent for the functor detecting flatness in dimensions at least a
fixed natural number.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (n : ℕ)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/-- The functor detecting flatness in dimensions at least `n` is an fpqc sheaf. -/
theorem flatInDimensionsFunctor_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (flatInDimensionsFunctor f ℱ n) := sorry

end AlgebraicGeometry.Scheme.Flattening
