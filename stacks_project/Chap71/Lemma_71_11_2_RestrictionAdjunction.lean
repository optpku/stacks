/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_2_Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction

/-!
# The actual extension/restriction adjunction on a represented scheme

The extension is the composite of scalar transport and the two module inverse
images. Its right adjoint is the existing restriction functor, including the
canonical identity-restriction comparison on the algebraic-space site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}}

/-- Identity postcomposition on the small etale site, by actual identity maps
of the represented schemes. -/
def identitySiteIso (Z : Over S) :
    Modules.restrictPostcompose (𝟙 (ofOver Z)) ≅ 𝟭 (smallEtaleSite (ofOver Z)) :=
  NatIso.ofComponents (fun W ↦
    { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 W.left) trivial sorry
      inv := MorphismProperty.CostructuredArrow.homMk (𝟙 W.left) trivial sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }) sorry

/-- The identity-on-sections ring comparison is compatible with that site isomorphism. -/
theorem identityRingMap (Z : Over S) :
    Modules.restrictStructureMap (𝟙 (ofOver Z)) ≫
      (Functor.sheafPushforwardContinuousNatTrans (identitySiteIso Z).inv
        RingCat.{u} (smallEtaleTopology (ofOver Z)) (smallEtaleTopology (ofOver Z))).app
          (structureSheaf (ofOver Z)) = 𝟙 (structureSheaf (ofOver Z)) := sorry

/-- Restriction along the identity is canonically the identity on modules. -/
def identityRestrictionIso (Z : Over S) :
    Modules.restrictFunctor (𝟙 (ofOver Z)) ≅ 𝟭 (ofOver Z).Modules :=
  SheafOfModules.pushforwardCongr₂
      (φ := Modules.restrictStructureMap (𝟙 (ofOver Z)))
      (identitySiteIso Z).symm (identityRingMap Z) ≪≫
    SheafOfModules.pushforwardId (structureSheaf (ofOver Z))

/-- The global-functions ring presentation on open subschemes. -/
def opensRingSheaf (Y : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology Y) RingCat.{u} :=
  ⟨Scheme.Site.structurePresheaf (Y.restrictFunctor ⋙ Over.forget Y),
    opensStructurePresheaf_isSheaf Y⟩

/-- The inverse ring map is the actual global-sections restriction comparison. -/
def opensInverseRingMap (Y : Scheme.{u}) : opensRingSheaf Y ⟶ Y.ringCatSheaf :=
  ⟨Functor.whiskerRight (@Scheme.restrictFunctorΓ Y).hom (forget₂ CommRingCat RingCat)⟩

/-- The two global-functions presentations are canonically isomorphic. -/
def opensRingIso (Y : Scheme.{u}) : Y.ringCatSheaf ≅ opensRingSheaf Y where
  hom := opensStructureToRingCatSheaf Y
  inv := opensInverseRingMap Y
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Scalar transport is the actual restriction-of-scalars equivalence. -/
def scalarsEquivalence (Y : Scheme.{u}) :
    Y.Modules ≌ SheafOfModules.{u} (opensRingSheaf Y) :=
  SheafOfModules.Restriction.equivalenceOfIso (opensRingIso Y)

/-- The open-to-etale module direct image has its geometric inverse-image adjoint. -/
instance opensPushforward_isRightAdjoint (Y : Scheme.{u}) :
    (smallEtaleToOpensRingedHom Y).modulePushforward.{u}.IsRightAdjoint := sorry

/-- The comparison of the two small etale sites has its module inverse image. -/
instance schemePushforward_isRightAdjoint (Z : Over S) :
    (schemeEtaleRingedHom Z).modulePushforward.{u}.IsRightAdjoint := sorry

/-- Extension of a scheme module through the actual three inverse-image functors. -/
def extension (Z : Over S) : Z.left.Modules ⥤ (ofOver Z).Modules :=
  (scalarsEquivalence Z.left).functor ⋙
    (smallEtaleToOpensRingedHom Z.left).modulePullback.{u} ⋙
      (schemeEtaleRingedHom Z).modulePullback.{u}

/-- The direct-image composite before the harmless identity restriction. -/
def restrictionBare (Z : Over S) : (ofOver Z).Modules ⥤ Z.left.Modules :=
  (schemeEtaleRingedHom Z).modulePushforward.{u} ⋙
    (smallEtaleToOpensRingedHom Z.left).modulePushforward.{u} ⋙
      opensToSchemeModules Z.left

/-- Remove identity restriction via its actual site-induced isomorphism. -/
def restrictionIsoBare (Z : Over S) : Modules.restrictToScheme Z ≅ restrictionBare Z :=
  Functor.isoWhiskerRight (identityRestrictionIso Z) (restrictionBare Z) ≪≫
    Functor.leftUnitor (restrictionBare Z)

/-- Composition of the three canonical adjunctions. -/
def extensionAdjunctionBare (Z : Over S) : extension Z ⊣ restrictionBare Z :=
  ((scalarsEquivalence Z.left).toAdjunction.comp
    (RingedSite.Hom.modulePullbackPushforwardAdjunction
      (smallEtaleToOpensRingedHom Z.left))).comp
    (RingedSite.Hom.modulePullbackPushforwardAdjunction (schemeEtaleRingedHom Z))

/-- The canonical extension/restriction adjunction, with no chosen comparison maps. -/
def extensionAdjunction (Z : Over S) : extension Z ⊣ Modules.restrictToScheme Z :=
  (extensionAdjunctionBare Z).ofNatIsoRight (restrictionIsoBare Z).symm

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
