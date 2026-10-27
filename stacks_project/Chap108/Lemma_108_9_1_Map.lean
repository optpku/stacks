/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Functor

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The Picard sheaf on schemes over the ambient base scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.functorOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S},
    (X ⟶ B) → Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
