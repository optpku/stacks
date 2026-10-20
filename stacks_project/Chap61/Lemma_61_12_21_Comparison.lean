module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleComparison

universe u

#check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison.restrictionIsEquivalence :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine S],
      CategoryTheory.Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.ProEt.affineIndEtaleRestriction S))
