module

public import ReasLib.AlgebraicGeometry.EllipticCurve.WeierstrassCover
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 105.6.1. The classifying morphism of the universal Weierstrass family is smooth
and surjective. -/
@[stacks 072T] #check
  (AlgebraicGeometry.WeierstrassScheme.classifying_smooth_surjective :
    Groupoids.Hom.SmoothOnSchemes AlgebraicGeometry.WeierstrassScheme.classifying.{u} ∧
      AlgebraicGeometry.EllipticCurve.Moduli.surjectiveOnSchemes
        AlgebraicGeometry.WeierstrassScheme.classifying.{u})
