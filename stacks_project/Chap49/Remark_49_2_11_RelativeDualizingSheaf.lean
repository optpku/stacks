/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Relative dualizing sheaf API compatibility bridge. -/
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f], Type (u + 1))
