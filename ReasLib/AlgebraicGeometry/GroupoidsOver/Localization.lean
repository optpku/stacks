/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AssociatedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.OverPostScheme
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Sites.Ringed.Equivalence
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Ringed localization of groupoid fibrations

Localization of the associated site at an object identifies its restricted
structure sheaf with the structure sheaf of the big site of the underlying scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The restricted structure presheaf is naturally isomorphic to the
global-sections presheaf of the composite realization on the slice category. -/
def localizationStructurePresheafIso (𝒳 : GroupoidsOver S) (τ : StandardTopology)
    (x : 𝒳.total) :
    ((associatedStructureSheaf 𝒳 τ).over x).obj ≅
      Scheme.Site.structurePresheaf (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S) :=
  isoWhiskerLeft (Over.forget x).op
      ((𝒳.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
          (𝒳.associatedTopology τ) (τ.overTopology S)).app
        (StandardTopology.Big.structureSheaf τ S)) ≪≫
    (associator (Over.forget x).op 𝒳.p.op
        (StandardTopology.Big.structureSheaf τ S).obj).symm ≪≫
    (associator ((Over.forget x).op ⋙ 𝒳.p.op) (Over.forget S).op
        (Scheme.Γ ⋙ forget₂ CommRingCat RingCat)).symm ≪≫
    isoWhiskerRight (associator (Over.forget x).op 𝒳.p.op (Over.forget S).op)
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat) ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (Over.forget x).op ((𝒳.p).opComp (Over.forget S)).symm)
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat) ≪≫
    isoWhiskerRight ((Over.forget x).opComp (𝒳.p ⋙ Over.forget S)).symm
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat)

/-- Sections of the restricted structure sheaf agree with global sections
of the composite realization on each object of the slice. -/
theorem localizationStructurePresheafIso_obj (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) (y : Over x) :
    ((associatedStructureSheaf 𝒳 τ).over x).obj.obj (op y) =
      (Scheme.Site.structurePresheaf
        (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S)).obj (op y) :=
  sorry

/-- The identity on underlying schemes induces the canonical map from the
restricted structure sheaf to the pushforward of the big structure sheaf. -/
def overPostSchemeRingedSiteHom_structureSheafMap (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    (associatedStructureSheaf 𝒳 τ).over x ⟶
      (RingedSiteMap.pushforward (overPostScheme 𝒳.p x)
        (overPostScheme.isMorphismOfSites 𝒳.p x τ)).obj
        (StandardTopology.Big.structureSheaf τ (𝒳.p.obj x).left) :=
  { hom :=
      (localizationStructurePresheafIso 𝒳 τ x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S)
          (Over.forget (𝒳.p.obj x).left)
          (overPostScheme 𝒳.p x) (𝟙 _) }

/-- The underlying presheaf comparison is reassociation followed by the
global-sections map induced by the identity on underlying schemes. -/
theorem overPostSchemeRingedSiteHom_structureSheafMap_hom (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    (overPostSchemeRingedSiteHom_structureSheafMap 𝒳 τ x).hom =
      (localizationStructurePresheafIso 𝒳 τ x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S)
          (Over.forget (𝒳.p.obj x).left)
          (overPostScheme 𝒳.p x) (𝟙 _) :=
  sorry

/-- The canonical ringed-site map has base functor from the localized associated
site to the big site of the underlying scheme and the identity-induced sheaf map. -/
def overPostSchemeRingedSiteHom (𝒳 : GroupoidsOver S) (τ : StandardTopology)
    (x : 𝒳.total) :
    RingedSiteMap (τ.overTopology (𝒳.p.obj x).left)
      (StandardTopology.Big.structureSheaf τ (𝒳.p.obj x).left)
      ((𝒳.associatedTopology τ).over x) ((associatedStructureSheaf 𝒳 τ).over x) where
  base := overPostScheme 𝒳.p x
  isMorphismOfSites := overPostScheme.isMorphismOfSites 𝒳.p x τ
  structureSheafMap := overPostSchemeRingedSiteHom_structureSheafMap 𝒳 τ x

/-- The base of the canonical ringed localization map is postcomposition with
the projection followed by the iterated-slice comparison. -/
theorem overPostSchemeRingedSiteHom_base (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    (overPostSchemeRingedSiteHom 𝒳 τ x).base = overPostScheme 𝒳.p x :=
  sorry

/-- The structure-sheaf map of the ringed localization map is the canonical
comparison induced by the identity on underlying schemes. -/
theorem overPostSchemeRingedSiteHom_structureSheafMap_eq (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    (overPostSchemeRingedSiteHom 𝒳 τ x).structureSheafMap =
      overPostSchemeRingedSiteHom_structureSheafMap 𝒳 τ x :=
  sorry

/-- Localization at an object of a category fibred in groupoids is equivalent,
as a ringed site, to the big site of its underlying scheme. -/
theorem overPostSchemeRingedSiteHom_isEquivalence (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    RingedSiteMap.IsEquivalence (overPostSchemeRingedSiteHom 𝒳 τ x) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
