/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_11_2_Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.PresentationComparison
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
