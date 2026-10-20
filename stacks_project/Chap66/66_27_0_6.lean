module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineRingedLocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S}
  (f : AlgebraicSpace.ofOver U ⟶ Y) [AlgebraicSpace.Etale f] [IsAffine U.left]

/- 66.27.0.6: if `f : ofOver U ⟶ Y` is étale and `U` is affine, the canonical equivalence
of affine étale sites identifies the structure sheaf of `ofOver U` with the restriction
of the structure sheaf of `Y` to the slice over `affineEtaleSite.mk f`. -/
@[stacks 04M3] #check
  (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationIso f :
      AlgebraicSpace.affineStructureSheaf (AlgebraicSpace.ofOver U) ≅
        ((AlgebraicSpace.affineEtaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
          (AlgebraicSpace.affineEtaleTopology (AlgebraicSpace.ofOver U))
          ((AlgebraicSpace.affineEtaleTopology Y).over (AlgebraicSpace.affineEtaleSite.mk f))).obj
          ((AlgebraicSpace.affineStructureSheaf Y).over (AlgebraicSpace.affineEtaleSite.mk f)))

#check
  (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationEquiv f :
      AlgebraicSpace.affineEtaleSite (AlgebraicSpace.ofOver U) ≌
        Over (AlgebraicSpace.affineEtaleSite.mk f))

#check
  (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationEquiv_functor f :
      (AlgebraicSpace.affineEtaleLocalizationEquiv f).functor =
        AlgebraicSpace.affineEtaleLocalizationFunctor f)
