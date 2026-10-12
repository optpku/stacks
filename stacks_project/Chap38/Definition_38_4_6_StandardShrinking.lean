/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.StandardShrinking

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- The support-point standard-shrinking API is re-exported from its shared owner. -/
#check (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAt.StandardShrinking :
  {S : Scheme.{u}} → {X : Over S} → {ℱ : X.left.Modules} →
    [LocallyOfFiniteType X.hom] → [ℱ.IsQuasicoherent] → [ℱ.IsFiniteType] →
    {x : X.left} → (D : AlgebraicGeometry.Scheme.Modules.OneStepDevissageAt X ℱ x) →
      Type (u + 1))
