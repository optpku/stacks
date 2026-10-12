/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAt

open AlgebraicGeometry CategoryTheory

universe u

/- The support-point specialization of a complete dévissage remains available through its
reusable mathematical owner. -/
#check (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt :
  {S X : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) →
    [LocallyOfFiniteType f] → [F.IsQuasicoherent] → [F.IsFiniteType] →
      (x : X) → Type (u + 1))
