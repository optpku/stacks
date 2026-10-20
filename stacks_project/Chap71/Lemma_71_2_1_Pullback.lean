/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemePullback

/-!
# Scheme-chart module pullback

Typed source-facing checks of the canonical module API.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackToScheme :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S},
    (ofOver U ⟶ X) → X.Modules → U.left.Modules)
