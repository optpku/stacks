/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Schemes admitting an ample invertible module

This leaf exposes the source-facing compatibility spelling for the canonical
`Scheme.Modules.HasAmpleInvertibleModule` predicate.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Compatibility spelling for a scheme admitting an ample invertible module. -/
abbrev HasAmpleInvertibleSheaf
    (X : Scheme.{u}) [MonoidalCategory X.Modules] : Prop :=
  Modules.HasAmpleInvertibleModule X

end AlgebraicGeometry.Scheme
