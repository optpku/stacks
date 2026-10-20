/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening

/-!
# The fpqc sheaf property for the flattening functor on algebraic spaces

This module records fpqc descent for the functor detecting flatness after base
change to a scheme over an algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [ℱ.IsQuasicoherent]

/-- The flattening functor of a quasi-coherent module is an fpqc sheaf on
schemes over `Y`. -/
theorem functor_isSheaf_fpqc :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology Y) (functor f ℱ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Flattening
