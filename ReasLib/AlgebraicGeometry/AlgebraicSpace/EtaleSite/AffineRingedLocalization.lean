module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineStructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineLocalization

/-!
# Structure sheaves under affine étale localization

For an étale morphism from an affine scheme, the canonical localization functor
identifies the affine structure sheaf with the restriction of the target structure sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S}

/-- The affine structure sheaf of an affine scheme is isomorphic to the restricted
structure sheaf along the canonical affine étale localization functor. -/
def affineEtaleLocalizationIso (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    affineStructureSheaf (ofOver U) ≅
      ((affineEtaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (affineEtaleTopology (ofOver U))
        ((affineEtaleTopology Y).over (affineEtaleSite.mk f))).obj
        ((affineStructureSheaf Y).over (affineEtaleSite.mk f)) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- The forward affine étale structure-sheaf comparison is the identity on sections. -/
@[simp]
theorem affineEtaleLocalizationIso_hom_app
    (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left]
    (V : (affineEtaleSite (ofOver U))ᵒᵖ) :
    (affineEtaleLocalizationIso f).hom.hom.app V = 𝟙 _ :=
  rfl

/-- The inverse affine étale structure-sheaf comparison is the identity on sections. -/
@[simp]
theorem affineEtaleLocalizationIso_inv_app
    (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left]
    (V : (affineEtaleSite (ofOver U))ᵒᵖ) :
    (affineEtaleLocalizationIso f).inv.hom.app V = 𝟙 _ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
