module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Small

/-!
# Enough points for scheme sites

This module records enough-points results for the standard small, big, and
affine-over sites associated with a scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The small affine Zariski site of a scheme has enough points. -/
instance hasEnoughPoints_smallAffineZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (smallAffineZariskiTopology S) :=
  sorry

/-- The small Zariski site of a scheme has enough points. -/
instance hasEnoughPoints_smallZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (smallZariskiTopology S) :=
  sorry

/-- The small affine étale site of a scheme has enough points. -/
instance hasEnoughPoints_smallAffineEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (AffineEtale.topology S) :=
  sorry

/-- The small étale site of a scheme has enough points. -/
theorem hasEnoughPoints_smallEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u} (smallEtaleTopology S) :=
  inferInstance

/-- The big Zariski site over a scheme has enough points. -/
instance hasEnoughPoints_bigZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (zariskiTopology.over S) :=
  sorry

/-- The affine-over Zariski site of a scheme has enough points. -/
instance hasEnoughPoints_affineZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (zariskiTopology.over S)) :=
  sorry

/-- The big étale site over a scheme has enough points. -/
instance hasEnoughPoints_bigEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology (@Etale)) :=
  sorry

/-- The affine-over étale site of a scheme has enough points. -/
instance hasEnoughPoints_affineEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (S.overGrothendieckTopology (@Etale))) :=
  sorry

/-- The big smooth site over a scheme has enough points. -/
instance hasEnoughPoints_bigSmooth (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology (@Smooth)) :=
  sorry

/-- The affine-over smooth site of a scheme has enough points. -/
instance hasEnoughPoints_affineSmooth (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (S.overGrothendieckTopology (@Smooth))) :=
  sorry

/-- The big syntomic site over a scheme has enough points. -/
instance hasEnoughPoints_bigSyntomic (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology (@Syntomic)) :=
  sorry

/-- The affine-over syntomic site of a scheme has enough points. -/
instance hasEnoughPoints_affineSyntomic (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (S.overGrothendieckTopology (@Syntomic))) :=
  sorry

/-- The big fppf site over a scheme has enough points. -/
instance hasEnoughPoints_bigFppf (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (fppfTopology.over S) :=
  sorry

/-- The affine-over fppf site of a scheme has enough points. -/
instance hasEnoughPoints_affineFppf (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (fppfTopology.over S)) :=
  sorry

end AlgebraicGeometry.Scheme
