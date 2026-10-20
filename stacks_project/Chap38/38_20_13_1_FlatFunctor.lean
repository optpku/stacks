/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening

/-!
# The flattening functor of a quasicoherent module

This module provides the source-facing base-change notation for the flattening functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The pullback of `ℱ` to the scheme obtained by changing the base along an `S`-scheme `T`. -/
abbrev baseChange (T : Over S) :
    (CategoryTheory.Limits.pullback f T.hom : Scheme.{u}).Modules :=
  Scheme.Modules.baseChangeModule f T.hom ℱ

end AlgebraicGeometry.Scheme.Modules.Flattening
