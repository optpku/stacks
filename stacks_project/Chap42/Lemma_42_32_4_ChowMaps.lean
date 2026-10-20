module

public import ReasLib.AlgebraicGeometry.ChowGroup.LineBundle.ZeroSection

@[expose] public section

open CategoryTheory

universe u

/- The Chow-map compatibility module exposes proper pushforward along the associated
line-bundle zero section. -/
#check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pushforward :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P] (k : ℤ),
      AlgebraicGeometry.RelativeChow δ X k →+
        @AlgebraicGeometry.RelativeChow S inferInstance δ inferInstance
          (AlgebraicGeometry.Scheme.AssociatedVectorBundle.totalOver X ℒ P)
          (AlgebraicGeometry.Scheme.AssociatedVectorBundle.totalOver_locallyOfFiniteType
            X ℒ P) k)
