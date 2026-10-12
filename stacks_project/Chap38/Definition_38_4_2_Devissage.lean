/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
