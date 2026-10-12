/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.QCohStack

/-! Compatibility import for the `QCohStack` category API. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- The promoted owner exports the complete category API under its existing names. -/
#check (AlgebraicGeometry.QCohStack.homSigma :
  ∀ {S : Scheme.{u}} (x y : AlgebraicGeometry.QCohStack.Obj S),
    (x ⟶ y) ≃
      Σ (f : x.base ⟶ y.base),
        ((AlgebraicGeometry.Scheme.QCoh.pullback f.left).obj y.sheaf ⟶ x.sheaf))
