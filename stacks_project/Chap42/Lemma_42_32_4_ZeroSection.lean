module

public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle.ZeroSection

@[expose] public section

open CategoryTheory

universe u

/- The zero-section compatibility module exposes the reusable associated-line-bundle
construction. -/
#check
  (AlgebraicGeometry.Scheme.AssociatedVectorBundle.zeroSection :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S)
      (ℒ : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      X.left ⟶ AlgebraicGeometry.Scheme.associatedVectorBundle ℒ P)
