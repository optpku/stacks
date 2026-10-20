/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage

/-!
# One-step dévissages

This compatibility module re-exports and checks the shared one-step
dévissage API.
-/

universe u

namespace AlgebraicGeometry.Scheme.Modules

#check (AlgebraicGeometry.Scheme.Modules.OneStepDevissage :
  {S : Scheme.{u}} → (X : CategoryTheory.Over S) → (F : X.left.Modules) →
    [LocallyOfFiniteType X.hom] → [F.IsQuasicoherent] → [F.IsFiniteType] →
    (s : S) → Type (u + 1))

end AlgebraicGeometry.Scheme.Modules
