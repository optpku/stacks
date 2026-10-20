module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.Point.Enough
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.AffineComparison

/-!
# Enough points of pro-étale sites

The big, small, and affine pro-étale sites of a scheme have enough points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

/-- The big pro-étale topology on schemes has enough points. -/
instance hasEnoughPoints_proetale :
    GrothendieckTopology.HasEnoughPoints.{u + 2}
      (proetaleTopology : GrothendieckTopology Scheme.{u}) :=
  sorry

/-- The big pro-étale topology of schemes over `S` has enough points. -/
instance hasEnoughPoints_proetaleOver (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 2} (proetaleTopology.over S) :=
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.ProEt

/-- The small pro-étale topology of a scheme has enough points. -/
instance hasEnoughPoints (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 2} (topology S) :=
  sorry

/-- The small affine pro-étale topology of a scheme has enough points. -/
instance hasEnoughPoints_affine (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 2} (affineTopology S) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The chosen big affine pro-étale topology of a scheme has enough points. -/
instance hasEnoughPoints_bigAffine (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology.HasEnoughPoints.{max (max u v + 1) (v + 1)}
      (bigAffineTopology X S) :=
  sorry

end AlgebraicGeometry.ChosenBigProetaleSite
