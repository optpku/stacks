/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A sheaf of modules on a scheme is quasi-coherent exactly when its restriction
to every affine open has an invertible canonical morphism from the tilde construction. -/
theorem isQuasicoherent_iff_forall_affineOpen_isTilde {X : Scheme.{u}} (F : X.Modules) :
    F.IsQuasicoherent ↔
      ∀ U : X.affineOpens, IsIso (F.restrict U.property.fromSpec).fromTildeΓ :=
  sorry

end AlgebraicGeometry.Scheme.Modules
