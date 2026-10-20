/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAt

universe u

open AlgebraicGeometry

/- Compatibility re-export of one-step dévissages at a point. -/
#check (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAt :
  {S : Scheme.{u}} → (X : CategoryTheory.Over S) → (ℱ : X.left.Modules) →
    [LocallyOfFiniteType X.hom] → [ℱ.IsQuasicoherent] → [ℱ.IsFiniteType] →
      (x : X.left) → Type (u + 1))
