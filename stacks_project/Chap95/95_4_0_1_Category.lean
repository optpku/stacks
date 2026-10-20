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
