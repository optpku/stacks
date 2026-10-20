/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization

/-!
# Big étale ringed site of an algebraic space

The structure sheaf `𝒪` on `(Spaces/X)_étale` is the global-sections sheaf
`U ↦ Γ(U, 𝒪_U)`, not `π_X⁻¹ 𝒪_X`. Restriction is the equalizer-lift of the
scheme-level map on the chosen atlas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.EffectiveEpi
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Atlas

variable {S : Scheme.{u}}

/-- Relocalization is a morphism of sites from the small étale site to the big étale slice. -/
instance relocalizationFunctor_isMorphismOfSites {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    IsMorphismOfSites (smallEtaleTopology Y) (overEtaleTopology X)
      (relocalizationFunctor f) :=
  sorry

/-- Recover a morphism of schemes over `S` from a morphism of the associated algebraic spaces. -/
private def ofOverHomPreimage {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- The atlas of `ofOver T` as a morphism of schemes over `S`. -/
private def ofOverAtlas (T : Over S) : (chosenPresentation (ofOver T)).U ⟶ T :=
  ofOverHomPreimage (chosenPresentation (ofOver T)).atlas

/-- The two presentation restrictions of `ofOver T` agree after restriction from `T`. -/
private theorem ofOverGlobalSections_equalizes (T : Over S) :
    (ofOverAtlas T).left.appTop ≫ (chosenPresentation (ofOver T)).tAppTop =
      (ofOverAtlas T).left.appTop ≫ (chosenPresentation (ofOver T)).sAppTop :=
  sorry

/-- The identification `Γ(T, 𝒪_T) ⟶ Γ(ofOver T, 𝒪)` on a representable algebraic space. -/
@[no_expose] def ofOverGlobalSections (T : Over S) :
    Γ(T.left, ⊤) ⟶ globalSectionsRing (ofOver T) :=
  equalizer.lift (ofOverAtlas T).left.appTop (ofOverGlobalSections_equalizes T)

/-- `ofOverGlobalSections T` lifts restriction along the chosen atlas of `ofOver T`. -/
private theorem ofOverGlobalSections_comp_ι (T : Over S) :
    ofOverGlobalSections T ≫ globalSectionsRing_ι (ofOver T) =
      (ofOverAtlas T).left.appTop :=
  sorry

/-- The atlas of `Y`, viewed as a morphism of sheaves into `X`. -/
private def atlasToX {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    yoneda.obj (chosenPresentation Y).U ⟶ X.functorOfPoints :=
  (chosenPresentation Y).atlas ≫ f

/-- `atlasToX f` is the chosen atlas of `Y` composed with `f`. -/
private theorem atlasToX_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasToX f = (chosenPresentation Y).atlas ≫ f :=
  rfl

/-- The fibre product of the chosen atlas of `Y` with the chosen atlas of `X`. -/
private def atlasPullback {X Y : AlgebraicSpace S} (f : Y ⟶ X) : Over S :=
  (chosenPresentation X).atlas_etale.rep.pullback (atlasToX f)

/-- Projection from the atlas fibre product to the chosen atlas of `Y`. -/
private def atlasPullbackToY {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasPullback f ⟶ (chosenPresentation Y).U :=
  (chosenPresentation X).atlas_etale.rep.snd (atlasToX f)

/-- Projection from the atlas fibre product to the chosen atlas of `X`. -/
private def atlasPullbackToX {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasPullback f ⟶ (chosenPresentation X).U :=
  (chosenPresentation X).atlas_etale.rep.fst' (atlasToX f)

/-- The underlying scheme morphism of `atlasPullbackToY f`. -/
private def atlasPullbackToYScheme {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (atlasPullback f).left ⟶ (chosenPresentation Y).U.left :=
  (atlasPullbackToY f).left

/-- The underlying scheme morphism of `atlasPullbackToX f`. -/
private def atlasPullbackToXScheme {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (atlasPullback f).left ⟶ (chosenPresentation X).U.left :=
  (atlasPullbackToX f).left

/-- `atlasPullbackToYScheme f` is étale. -/
private instance atlasPullbackToYScheme_etale {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    _root_.AlgebraicGeometry.Etale (atlasPullbackToYScheme f) :=
  (chosenPresentation X).atlas_etale.property_snd (atlasToX f)

/-- `atlasPullbackToYScheme f` is surjective. -/
private instance atlasPullbackToYScheme_surjective {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    _root_.AlgebraicGeometry.Surjective (atlasPullbackToYScheme f) :=
  sorry

/-- The scheme morphism from the atlas fibre product to `Spec Γ(X, 𝒪_X)`. -/
private def atlasPullbackToSpecGamma {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (atlasPullback f).left ⟶ Spec (globalSectionsRing X) :=
  atlasPullbackToXScheme f ≫ atlasToSpec_scheme X

/-- `atlasPullbackToSpecGamma f` is `atlasPullbackToX f` followed by `atlasToSpec_scheme X`. -/
private theorem atlasPullbackToSpecGamma_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasPullbackToSpecGamma f =
      (atlasPullbackToX f).left ≫ atlasToSpec_scheme X :=
  rfl

/-- Morphisms that equalize `atlasPullbackToY f` also equalize `atlasPullbackToSpecGamma f`. -/
private theorem atlasPullbackToSpecGamma_descends {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (atlasPullback f).left)
    (hg : g₁ ≫ atlasPullbackToYScheme f = g₂ ≫ atlasPullbackToYScheme f) :
    g₁ ≫ atlasPullbackToSpecGamma f = g₂ ≫ atlasPullbackToSpecGamma f :=
  sorry

/-- The scheme morphism from the chosen atlas of `Y` to `Spec Γ(X, 𝒪_X)`, obtained by
descending the atlas fibre product along the étale surjection `atlasPullbackToY f`. -/
private def atlasYToSpecGamma {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (chosenPresentation Y).U.left ⟶ Spec (globalSectionsRing X) :=
  EffectiveEpi.desc (atlasPullbackToYScheme f) (atlasPullbackToSpecGamma f)
    (atlasPullbackToSpecGamma_descends f)

/-- `atlasYToSpecGamma f` is the effective-epi descent of `atlasPullbackToSpecGamma f`. -/
private theorem atlasYToSpecGamma_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasYToSpecGamma f =
      EffectiveEpi.desc (atlasPullbackToYScheme f) (atlasPullbackToSpecGamma f)
        (atlasPullbackToSpecGamma_descends f) :=
  rfl

/-- Scheme-level restriction `Γ(X) ⟶ Γ(U_Y)` along `f`, as `ΓSpecIso.inv` followed by
`appTop` of the descended map from the chosen atlas of `Y` to `Spec Γ(X)`. -/
private def globalSectionsToYAtlas {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ Γ((chosenPresentation Y).U.left, ⊤) :=
  (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫ (atlasYToSpecGamma f).appTop

/-- `globalSectionsToYAtlas f` is the `ΓSpec` adjunct of `atlasYToSpecGamma f`. -/
private theorem globalSectionsToYAtlas_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsToYAtlas f =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫ (atlasYToSpecGamma f).appTop :=
  rfl

/-- The two presentation restrictions of `Y` agree after the scheme-level atlas
restriction from `X`. -/
private theorem globalSectionsRingMap_equalizes {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsToYAtlas f ≫ (chosenPresentation Y).tAppTop =
      globalSectionsToYAtlas f ≫ (chosenPresentation Y).sAppTop :=
  sorry

/-- The map on global sections `Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)` induced by a morphism of algebraic
spaces, as the equalizer lift of the scheme-level map into Gamma of the chosen atlas
of `Y`. -/
@[no_expose] def globalSectionsRingMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  equalizer.lift (globalSectionsToYAtlas f) (globalSectionsRingMap_equalizes f)

/-- `globalSectionsRingMap f` lifts `globalSectionsToYAtlas f` through the equalizer
inclusion of `Γ(Y, 𝒪_Y)`. -/
private theorem globalSectionsRingMap_comp_ι {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRingMap f ≫ globalSectionsRing_ι Y = globalSectionsToYAtlas f :=
  sorry

/-- Restriction of atlas global sections along an identity is the identity. -/
theorem overEtaleStructurePresheaf_map_id (X : AlgebraicSpace S) (U : (Over X)ᵒᵖ) :
    (forget₂ CommRingCat RingCat).map
      (globalSectionsRingMap (𝟙 U).unop.left) =
      𝟙 ((forget₂ CommRingCat RingCat).obj (globalSectionsRing U.unop.left)) :=
  sorry

/-- Restriction of atlas global sections respects composition in the opposite slice. -/
theorem overEtaleStructurePresheaf_map_comp (X : AlgebraicSpace S)
    {U V W : (Over X)ᵒᵖ} (g : U ⟶ V) (h : V ⟶ W) :
    (forget₂ CommRingCat RingCat).map (globalSectionsRingMap (g ≫ h).unop.left) =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.unop.left) ≫
        (forget₂ CommRingCat RingCat).map (globalSectionsRingMap h.unop.left) :=
  sorry

/-- The ring presheaf on `(Spaces/X)_étale` with value `Γ(U, 𝒪_U)`. -/
def overEtaleStructurePresheaf (X : AlgebraicSpace S) :
    (Over X)ᵒᵖ ⥤ RingCat.{u} where
  obj U := (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.unop.left)
  map {U V} g :=
    (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.unop.left)
  map_id := overEtaleStructurePresheaf_map_id X
  map_comp := overEtaleStructurePresheaf_map_comp X

/-- The value of `overEtaleStructurePresheaf X` at `U` is `Γ(U.left, 𝒪_{U.left})`. -/
theorem overEtaleStructurePresheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (overEtaleStructurePresheaf X).obj (op U) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.left) :=
  rfl

/-- Restriction in `overEtaleStructurePresheaf X` is `globalSectionsRingMap` of the underlying
morphism of algebraic spaces. -/
theorem overEtaleStructurePresheaf_map (X : AlgebraicSpace S) {U V : Over X} (g : U ⟶ V) :
    (overEtaleStructurePresheaf X).map g.op =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.left) :=
  rfl

/-- The global-sections presheaf on `(Spaces/X)_étale` is a sheaf. -/
theorem overEtaleStructurePresheaf_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (overEtaleTopology X) (overEtaleStructurePresheaf X) :=
  sorry

/-- The structure sheaf `𝒪` on `(Spaces/X)_étale`, with value `U ↦ Γ(U, 𝒪_U)`. -/
def overEtaleStructureSheaf (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) RingCat.{u} :=
  ⟨overEtaleStructurePresheaf X, overEtaleStructurePresheaf_isSheaf X⟩

/-- On an algebraic space `U` over `X`, the big étale structure sheaf has value
`Γ(U, 𝒪_U)`. -/
theorem overEtaleStructureSheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (overEtaleStructureSheaf X).obj.obj (op U) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.left) :=
  rfl

/-- Restriction in `overEtaleStructureSheaf X` is `globalSectionsRingMap` of the underlying
morphism of algebraic spaces. -/
theorem overEtaleStructureSheaf_map (X : AlgebraicSpace S) {U V : Over X} (g : U ⟶ V) :
    (overEtaleStructureSheaf X).obj.map g.op =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.left) :=
  rfl

/-- The big étale ringed site `((Spaces/X)_étale, 𝒪)`. -/
abbrev overEtaleRingedSite (X : AlgebraicSpace S) : RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (overEtaleTopology X) (overEtaleStructureSheaf X)

/-- The structure sheaf of `overEtaleRingedSite X` is `overEtaleStructureSheaf X`. -/
theorem overEtaleRingedSite_structureSheaf (X : AlgebraicSpace S) :
    (overEtaleRingedSite X).structureSheaf = overEtaleStructureSheaf X :=
  rfl

/-- Scheme sections commute with restriction after passage to the atlas equalizer. -/
theorem smallToBigStructureSheafMap_naturality {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    {U V : (smallEtaleSite Y)ᵒᵖ} (g : U ⟶ V) :
    (structureSheaf Y).obj.map g ≫
        (forget₂ CommRingCat RingCat).map (ofOverGlobalSections V.unop.left) =
      (forget₂ CommRingCat RingCat).map (ofOverGlobalSections U.unop.left) ≫
        (((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleTopology Y) (overEtaleTopology X)).obj
            (overEtaleStructureSheaf X)).obj.map g :=
  sorry

/-- Direct-image form of `π_X^♯` / `i_f^♯`: on a scheme étale over `Y`, the source is
`Γ(U, 𝒪_U)` and the target is `Γ(U, 𝒪_U)` computed as an algebraic space. -/
def smallToBigStructureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheaf Y ⟶
      ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (overEtaleTopology X)).obj
        (overEtaleStructureSheaf X) :=
  InducedCategory.homMk
    { app := fun U ↦
        (forget₂ CommRingCat RingCat).map (ofOverGlobalSections U.unop.left)
      naturality := fun _ _ g ↦ smallToBigStructureSheafMap_naturality f g }

/-- The component of `smallToBigStructureSheafMap f` is `ofOverGlobalSections` of the
underlying scheme. -/
theorem smallToBigStructureSheafMap_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (smallToBigStructureSheafMap f).hom.app U =
      (forget₂ CommRingCat RingCat).map (ofOverGlobalSections U.unop.left) :=
  rfl

/-- The morphism of ringed sites `π_X : ((Spaces/X)_étale, 𝒪) ⟶ (X_étale, 𝒪_X)`, with
structure map the small-site identification `(π_* 𝒪)(U) = Γ(U, 𝒪_U) = 𝒪_X(U)`. -/
def etalePiRingedHom (X : AlgebraicSpace S) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite X) where
  base := relocalizationFunctor (𝟙 X)
  isMorphismOfSites := relocalizationFunctor_isMorphismOfSites (𝟙 X)
  structureSheafMap := smallToBigStructureSheafMap (𝟙 X)

/-- The base functor of `etalePiRingedHom X` is identity-base étale relocalization. -/
theorem etalePiRingedHom_base (X : AlgebraicSpace S) :
    (etalePiRingedHom X).base = relocalizationFunctor (𝟙 X) :=
  rfl

/-- The structure-sheaf map of `etalePiRingedHom X` is `smallToBigStructureSheafMap (𝟙 X)`. -/
theorem etalePiRingedHom_structureSheafMap (X : AlgebraicSpace S) :
    (etalePiRingedHom X).structureSheafMap = smallToBigStructureSheafMap (𝟙 X) :=
  rfl

/-- The morphism of ringed sites `i_f : (Y_étale, 𝒪_Y) ⟶ ((Spaces/X)_étale, 𝒪)`, with
structure map the identification `i_f^{-1} 𝒪 ≅ 𝒪_Y`. -/
def relocalizationRingedHom {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite Y) where
  base := relocalizationFunctor f
  isMorphismOfSites := relocalizationFunctor_isMorphismOfSites f
  structureSheafMap := smallToBigStructureSheafMap f

/-- The base functor of `relocalizationRingedHom f` is étale relocalization along `f`. -/
theorem relocalizationRingedHom_base {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (relocalizationRingedHom f).base = relocalizationFunctor f :=
  rfl

/-- The structure-sheaf map of `relocalizationRingedHom f` is `smallToBigStructureSheafMap f`. -/
theorem relocalizationRingedHom_structureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (relocalizationRingedHom f).structureSheafMap = smallToBigStructureSheafMap f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.Atlas

end

end
