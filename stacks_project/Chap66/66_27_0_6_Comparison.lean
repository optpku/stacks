/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import stacks_project.Chap66.«66_27_0_5_Comparison»
public import stacks_project.Chap66.«66_27_0_6_Site»

/-!
# Affine étale localization of affine étale ringed sites

An étale morphism `f : ofOver U ⟶ Y` from an affine scheme to an algebraic space identifies the
affine étale ringed site of `ofOver U` with the localization of the affine étale ringed site of
`Y` at the object `affineEtaleSite.mk f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S}

/-- Identity-on-sections map from the restricted structure sheaf of `Y` to the pushforward of
`𝒪` along `affineEtaleLocalizationInverse`. -/
def affineEtaleLocalizationIsoHomStructureSheaf (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    (affineStructureSheaf Y).over (affineEtaleSite.mk f) ⟶
      ((affineEtaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((affineEtaleTopology Y).over (affineEtaleSite.mk f))
        (affineEtaleTopology (ofOver U))).obj (affineStructureSheaf (ofOver U)) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := sorry }⟩

/-- Identity-on-sections map from `𝒪` on `X_affine,étale` to the pushforward of the restricted
structure sheaf of `Y` along `affineEtaleLocalizationFunctor`. -/
def affineEtaleLocalizationIsoInvStructureSheaf (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    affineStructureSheaf (ofOver U) ⟶
      ((affineEtaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (affineEtaleTopology (ofOver U))
        ((affineEtaleTopology Y).over (affineEtaleSite.mk f))).obj
        ((affineStructureSheaf Y).over (affineEtaleSite.mk f)) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := sorry }⟩

/-- The morphism of ringed sites from `(X_affine,étale, 𝒪_X)` to the localization of
`(Y_affine,étale, 𝒪_Y)` at `X`. -/
def affineEtaleLocalizationIsoHom (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    RingedSite.Hom (affineRingedSite (ofOver U))
      ((affineRingedSite Y).localization (affineEtaleSite.mk f)) where
  base := affineEtaleLocalizationInverse f
  structureSheafMap := affineEtaleLocalizationIsoHomStructureSheaf f

/-- The morphism of ringed sites from the localization of `(Y_affine,étale, 𝒪_Y)` at `X` to
`(X_affine,étale, 𝒪_X)`. -/
def affineEtaleLocalizationIsoInv (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    RingedSite.Hom ((affineRingedSite Y).localization (affineEtaleSite.mk f))
      (affineRingedSite (ofOver U)) where
  base := affineEtaleLocalizationFunctor f
  structureSheafMap := affineEtaleLocalizationIsoInvStructureSheaf f

/-- Identification of affine étale ringed sites
`(X_affine,étale, 𝒪_X) ≅ (Y_affine,étale / X, 𝒪_Y restricted)` along an étale morphism from an
affine scheme. -/
def affineEtaleLocalizationIso (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    affineRingedSite (ofOver U) ≅
      (affineRingedSite Y).localization (affineEtaleSite.mk f) where
  hom := affineEtaleLocalizationIsoHom f
  inv := affineEtaleLocalizationIsoInv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The base functor of the forward ringed-site morphism is `affineEtaleLocalizationInverse`. -/
@[simp]
theorem affineEtaleLocalizationIso_hom_base (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    (affineEtaleLocalizationIso f).hom.base = affineEtaleLocalizationInverse f :=
  rfl

/-- The base functor of the inverse ringed-site morphism is `affineEtaleLocalizationFunctor`. -/
@[simp]
theorem affineEtaleLocalizationIso_inv_base (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left] :
    (affineEtaleLocalizationIso f).inv.base = affineEtaleLocalizationFunctor f :=
  rfl

/-- The forward structure-sheaf comparison is the identity on sections. -/
@[simp]
theorem affineEtaleLocalizationIso_hom_structureSheaf_app
    (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left]
    (W : (Over (affineEtaleSite.mk f))ᵒᵖ) :
    ((affineEtaleLocalizationIso f).hom.structureSheafMap).hom.app W = 𝟙 _ :=
  rfl

/-- The inverse structure-sheaf comparison is the identity on sections. -/
@[simp]
theorem affineEtaleLocalizationIso_inv_structureSheaf_app
    (f : ofOver U ⟶ Y) [Etale f] [IsAffine U.left]
    (V : (affineEtaleSite (ofOver U))ᵒᵖ) :
    ((affineEtaleLocalizationIso f).inv.structureSheafMap).hom.app V = 𝟙 _ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
