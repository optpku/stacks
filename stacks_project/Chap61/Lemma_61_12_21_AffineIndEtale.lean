module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtale

universe u

#check
  (AlgebraicGeometry.Scheme.ProEt.affineIndEtaleTopology :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine S],
      CategoryTheory.GrothendieckTopology
        (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale S))
