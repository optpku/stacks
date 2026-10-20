/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.FiberIsoClasses

open CategoryTheory

universe u

/- The Picard projection to schemes over the base. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.toSchemesOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X B : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ B), AlgebraicGeometry.AlgebraicSpace.Picard.Obj f ⥤
      AlgebraicGeometry.AlgebraicSpace.CohStack.SchemesOver B)
