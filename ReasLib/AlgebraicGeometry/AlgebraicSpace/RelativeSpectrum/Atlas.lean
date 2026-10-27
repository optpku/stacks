/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

/-!
# Atlas restriction data for relative spectra

The chosen atlas and represented kernel pair reuse the public input and
presentation owners. Open images require an open map; an arrow on étale charts
also requires the actual commuting triangle over the algebraic space.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Functor CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

local instance : (MorphismProperty.over (@AlgebraicGeometry.Etale) (X := S)).IsStableUnderComposition :=
  inferInstanceAs ((MorphismProperty.inverseImage (@AlgebraicGeometry.Etale)
    (Over.forget S)).IsStableUnderComposition)

local instance : (MorphismProperty.over (@AlgebraicGeometry.Etale) (X := S)).IsStableUnderBaseChange where
  of_isPullback h hg := MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
    (h.map (Over.forget S)) hg

/-- An étale atlas scheme of an algebraic space, extracted from the atlas field. -/
abbrev atlasScheme (X : AlgebraicSpace S) : Over S :=
  AtlasInput.scheme X

/-- The atlas morphism `ofOver (atlasScheme X) ⟶ X`. -/
abbrev atlasHom (X : AlgebraicSpace S) : ofOver (atlasScheme X) ⟶ X :=
  AtlasInput.map X

/-- The atlas morphism is representable and étale as a presheaf morphism. -/
theorem atlasHom_presheaf_etale (X : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (atlasHom X) :=
  AtlasInput.representableEtale X

/-- The atlas morphism is étale as a morphism of algebraic spaces. -/
instance etale_atlasHom (X : AlgebraicSpace S) : Etale (atlasHom X) :=
  ⟨fun _ hφ ↦ MorphismProperty.comp_mem _ _ _ hφ (atlasHom_presheaf_etale X)⟩

/-- The scheme over `S` associated to an open of the atlas of `X`. -/
def atlasOpenOver (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) : Over S :=
  Over.mk (V.ι ≫ (atlasScheme X).hom)

/-- The open immersion of an atlas open, as a morphism over `S`. -/
def atlasOpenOverHom (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) :
    atlasOpenOver X V ⟶ atlasScheme X :=
  Over.homMk V.ι rfl

/-- An open immersion of the atlas remains étale after viewing it as a morphism of algebraic
spaces. -/
instance etale_ofOverMap_atlasOpenOverHom (X : AlgebraicSpace S)
    (V : (atlasScheme X).left.Opens) :
    Etale ((ofOverFunctor S).map (atlasOpenOverHom X V)) :=
  ⟨fun _ hφ ↦ MorphismProperty.comp_mem _ _ _ hφ
    (MorphismProperty.relative_map (F := yoneda)
      (show AlgebraicGeometry.Etale V.ι from inferInstance))⟩

/-- The composite of an atlas open with the atlas morphism is étale. -/
instance etale_atlasOpenHom (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) :
    Etale ((ofOverFunctor S).map (atlasOpenOverHom X V) ≫ atlasHom X) :=
  @AlgebraicGeometry.AlgebraicSpace.Etale.etale_comp S _ _
    ((ofOverFunctor S).map (atlasOpenOverHom X V)) _ (atlasHom X)
    (etale_ofOverMap_atlasOpenOverHom X V) (etale_atlasHom X)

/-- The small étale object of `X` associated to an open of its atlas. -/
def atlasOpenToSmallEtaleObj (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) :
    smallEtaleSite X :=
  smallEtaleSite.mk ((ofOverFunctor S).map (atlasOpenOverHom X V) ≫ atlasHom X)
    (etale_atlasOpenHom X V)

/-- The morphism of atlas opens over `S` induced by an inclusion of opens. -/
def atlasOpenOverMap (X : AlgebraicSpace S) {V W : (atlasScheme X).left.Opens}
    (i : V ⟶ W) : atlasOpenOver X V ⟶ atlasOpenOver X W :=
  Over.homMk ((atlasScheme X).left.homOfLE (leOfHom i)) (by
    change (atlasScheme X).left.homOfLE (leOfHom i) ≫
      (W.ι ≫ (atlasScheme X).hom) = V.ι ≫ (atlasScheme X).hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The functor from Zariski opens of an étale atlas of `X` to the small étale site of `X`. -/
def atlasOpenToSmallEtale (X : AlgebraicSpace S) :
    (atlasScheme X).left.Opens ⥤ smallEtaleSite X where
  obj := atlasOpenToSmallEtaleObj X
  map {V W} i :=
    MorphismProperty.CostructuredArrow.homMk (atlasOpenOverMap X i) trivial (by
      have h : atlasOpenOverMap X i ≫ atlasOpenOverHom X W = atlasOpenOverHom X V := by
        apply Over.OverMorphism.ext
        exact Scheme.homOfLE_ι _ (leOfHom i)
      change yoneda.map (atlasOpenOverMap X i) ≫
        (yoneda.map (atlasOpenOverHom X W) ≫ atlasHom X) =
        yoneda.map (atlasOpenOverHom X V) ≫ atlasHom X
      rw [← Category.assoc, ← Functor.map_comp, h])
  map_id V := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply Over.OverMorphism.ext
    exact Scheme.homOfLE_rfl _ _
  map_comp i j := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply Over.OverMorphism.ext
    exact (Scheme.homOfLE_homOfLE _ (leOfHom i) (leOfHom j)).symm

/-- Restrict a small étale sheaf of commutative rings on `X` to the Zariski site of an étale
atlas of `X`. -/
def restrictToAtlasPresheaf {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (atlasScheme X).left.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (atlasOpenToSmallEtale X).op ⋙ F.obj

/-- Restrict an `𝒪_X`-algebra to the Zariski site of an étale atlas of `X`. -/
def restrictUnder {X : AlgebraicSpace S} (B : Under (commStructureSheaf X)) :
    Under (restrictToAtlasPresheaf (commStructureSheaf X)) :=
  Under.mk (whiskerLeft (atlasOpenToSmallEtale X).op (InducedCategory.Hom.hom B.hom))

/-- Restrict a morphism of `𝒪_X`-algebras to the Zariski site of an étale atlas of `X`. -/
def restrictUnderMap {X : AlgebraicSpace S} {B₁ B₂ : Under (commStructureSheaf X)}
    (α : B₁ ⟶ B₂) :
    restrictUnder B₁ ⟶ restrictUnder B₂ :=
  CategoryTheory.Under.homMk
    (whiskerLeft (atlasOpenToSmallEtale X).op (InducedCategory.Hom.hom α.right))
    (by
      change whiskerLeft _ _ ≫ whiskerLeft _ _ = whiskerLeft _ _
      rw [← whiskerLeft_comp]
      exact congrArg
        (fun f ↦ whiskerLeft (atlasOpenToSmallEtale X).op (InducedCategory.Hom.hom f))
        (Under.w α))

/-- The underlying sheaf morphism of `restrictUnderMap α` is whiskering along atlas opens. -/
theorem restrictUnderMap_right {X : AlgebraicSpace S} {B₁ B₂ : Under (commStructureSheaf X)}
    (α : B₁ ⟶ B₂) :
    (restrictUnderMap α).right =
      whiskerLeft (atlasOpenToSmallEtale X).op (InducedCategory.Hom.hom α.right) :=
  rfl

/-- The stored atlas supplies its canonical étale equivalence relation. -/
def relativeSpectrumAtlasPresentation (X : AlgebraicSpace S) : Presentation X :=
  Presentation.ofAtlas (AtlasInput.map X)
    (AtlasInput.representableEtale X) (AtlasInput.locallySurjective X)

/-- The kernel pair scheme `U ×_X U` of the chosen étale atlas of `X`. -/
def atlasKernelPair (X : AlgebraicSpace S) : Over S :=
  (relativeSpectrumAtlasPresentation X).R.left

/-- `atlasKernelPair X` is the source of the represented kernel pair of `atlasHom X`. -/
theorem atlasKernelPair_eq (X : AlgebraicSpace S) :
    atlasKernelPair X = (relativeSpectrumAtlasPresentation X).R.left :=
  rfl

/-- The first projection `t : U ×_X U ⟶ U` of the atlas kernel pair. -/
def atlasKernelPair_t (X : AlgebraicSpace S) : atlasKernelPair X ⟶ atlasScheme X :=
  (relativeSpectrumAtlasPresentation X).R.t

/-- The second projection `s : U ×_X U ⟶ U` of the atlas kernel pair. -/
def atlasKernelPair_s (X : AlgebraicSpace S) : atlasKernelPair X ⟶ atlasScheme X :=
  (relativeSpectrumAtlasPresentation X).R.s

/-- `atlasKernelPair_t X` is the first projection of the represented kernel pair. -/
theorem atlasKernelPair_t_eq (X : AlgebraicSpace S) :
    atlasKernelPair_t X = (relativeSpectrumAtlasPresentation X).R.t :=
  rfl

/-- `atlasKernelPair_s X` is the second projection of the represented kernel pair. -/
theorem atlasKernelPair_s_eq (X : AlgebraicSpace S) :
    atlasKernelPair_s X = (relativeSpectrumAtlasPresentation X).R.s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSpectrumAtlas_isPullback (X : AlgebraicSpace S) :
    IsPullback (yoneda.map (atlasKernelPair_t X)) (yoneda.map (atlasKernelPair_s X))
      (atlasHom X) (atlasHom X) := by
  let h := atlasHom_presheaf_etale X
  change IsPullback
    (yoneda.map (prod.lift (h.rep.fst' (atlasHom X)) (h.rep.snd (atlasHom X)) ≫ prod.fst))
    (yoneda.map (prod.lift (h.rep.fst' (atlasHom X)) (h.rep.snd (atlasHom X)) ≫ prod.snd))
    (atlasHom X) (atlasHom X)
  rw [prod.lift_fst, prod.lift_snd]
  exact h.rep.isPullback' (atlasHom X)

/-- The two atlas kernel-pair projections become equal after composition with `atlasHom X`. -/
theorem atlasKernelPair_t_comp_eq_s_comp (X : AlgebraicSpace S) :
    (ofOverFunctor S).map (atlasKernelPair_t X) ≫ atlasHom X =
      (ofOverFunctor S).map (atlasKernelPair_s X) ≫ atlasHom X :=
  (relativeSpectrumAtlas_isPullback X).w

/-- The morphism `ofOver (U ×_X U) ⟶ X` induced by the atlas kernel pair. -/
def atlasKernelPairHom (X : AlgebraicSpace S) : ofOver (atlasKernelPair X) ⟶ X :=
  (ofOverFunctor S).map (atlasKernelPair_t X) ≫ atlasHom X

/-- `atlasKernelPairHom X` is the kernel-pair morphism of the atlas. -/
theorem atlasKernelPairHom_eq (X : AlgebraicSpace S) :
    atlasKernelPairHom X = (ofOverFunctor S).map (atlasKernelPair_t X) ≫ atlasHom X :=
  rfl

/-- The atlas kernel-pair morphism is étale. -/
instance etale_atlasKernelPairHom (X : AlgebraicSpace S) : Etale (atlasKernelPairHom X) :=
  ⟨fun _ hφ ↦ MorphismProperty.comp_mem _ _ _ hφ
    (MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map (F := yoneda)
        ((atlasHom_presheaf_etale X).property (atlasHom X) _ _
          (relativeSpectrumAtlas_isPullback X).flip))
      (atlasHom_presheaf_etale X))⟩

/-- The scheme over `S` associated to an open of the atlas kernel pair. -/
def kernelPairOpenOver (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) : Over S :=
  Over.mk (W.ι ≫ (atlasKernelPair X).hom)

/-- The open immersion of a kernel-pair open, as a morphism over `S`. -/
def kernelPairOpenOverHom (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) :
    kernelPairOpenOver X W ⟶ atlasKernelPair X :=
  Over.homMk W.ι rfl

/-- An open immersion of the atlas kernel pair remains étale as a morphism of algebraic spaces. -/
instance etale_ofOverMap_kernelPairOpenOverHom (X : AlgebraicSpace S)
    (W : (atlasKernelPair X).left.Opens) :
    Etale ((ofOverFunctor S).map (kernelPairOpenOverHom X W)) :=
  ⟨fun _ hφ ↦ MorphismProperty.comp_mem _ _ _ hφ
    (MorphismProperty.relative_map (F := yoneda)
      (show AlgebraicGeometry.Etale W.ι from inferInstance))⟩

/-- The composite of a kernel-pair open with the atlas kernel-pair morphism is étale. -/
instance etale_kernelPairOpenHom (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) :
    Etale ((ofOverFunctor S).map (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X) :=
  @AlgebraicGeometry.AlgebraicSpace.Etale.etale_comp S _ _
    ((ofOverFunctor S).map (kernelPairOpenOverHom X W)) _ (atlasKernelPairHom X)
    (etale_ofOverMap_kernelPairOpenOverHom X W) (etale_atlasKernelPairHom X)

/-- The small étale object of `X` associated to an open of its atlas kernel pair. -/
def kernelPairOpenToSmallEtaleObj (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) :
    smallEtaleSite X :=
  smallEtaleSite.mk ((ofOverFunctor S).map (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X)
    (etale_kernelPairOpenHom X W)

/-- The structural morphism of `kernelPairOpenToSmallEtaleObj X W` is the composite with
`atlasKernelPairHom X`. -/
theorem kernelPairOpenToSmallEtaleObj_hom (X : AlgebraicSpace S)
    (W : (atlasKernelPair X).left.Opens) :
    (kernelPairOpenToSmallEtaleObj X W).hom =
      (ofOverFunctor S).map (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X :=
  rfl

/-- The morphism of kernel-pair opens over `S` induced by an inclusion of opens. -/
def kernelPairOpenOverMap (X : AlgebraicSpace S) {V W : (atlasKernelPair X).left.Opens}
    (i : V ⟶ W) : kernelPairOpenOver X V ⟶ kernelPairOpenOver X W :=
  Over.homMk ((atlasKernelPair X).left.homOfLE (leOfHom i)) (by
    change (atlasKernelPair X).left.homOfLE (leOfHom i) ≫
      (W.ι ≫ (atlasKernelPair X).hom) = V.ι ≫ (atlasKernelPair X).hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The functor from Zariski opens of `U ×_X U` to the small étale site of `X`. -/
def kernelPairOpenToSmallEtale (X : AlgebraicSpace S) :
    (atlasKernelPair X).left.Opens ⥤ smallEtaleSite X where
  obj := kernelPairOpenToSmallEtaleObj X
  map {V W} i :=
    MorphismProperty.CostructuredArrow.homMk (kernelPairOpenOverMap X i) trivial (by
      have h : kernelPairOpenOverMap X i ≫ kernelPairOpenOverHom X W =
          kernelPairOpenOverHom X V := by
        apply Over.OverMorphism.ext
        exact Scheme.homOfLE_ι _ (leOfHom i)
      change yoneda.map (kernelPairOpenOverMap X i) ≫
        (yoneda.map (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X) =
        yoneda.map (kernelPairOpenOverHom X V) ≫ atlasKernelPairHom X
      rw [← Category.assoc, ← Functor.map_comp, h])
  map_id W := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply Over.OverMorphism.ext
    exact Scheme.homOfLE_rfl _ _
  map_comp i j := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply Over.OverMorphism.ext
    exact (Scheme.homOfLE_homOfLE _ (leOfHom i) (leOfHom j)).symm

/-- On objects, `kernelPairOpenToSmallEtale X` is `kernelPairOpenToSmallEtaleObj X`. -/
theorem kernelPairOpenToSmallEtale_obj (X : AlgebraicSpace S)
    (W : (atlasKernelPair X).left.Opens) :
    (kernelPairOpenToSmallEtale X).obj W = kernelPairOpenToSmallEtaleObj X W :=
  rfl

/-- Restriction of a small étale sheaf of commutative rings on `X` to the Zariski site of
`U ×_X U`. -/
def restrictToKernelPairPresheaf {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (atlasKernelPair X).left.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (kernelPairOpenToSmallEtale X).op ⋙ F.obj

/-- `restrictToKernelPairPresheaf F` is precomposition with `kernelPairOpenToSmallEtale`. -/
theorem restrictToKernelPairPresheaf_eq {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    restrictToKernelPairPresheaf F = (kernelPairOpenToSmallEtale X).op ⋙ F.obj :=
  rfl

/-- The atlas kernel-pair first projection is étale. -/
instance atlasKernelPair_t_etale (X : AlgebraicSpace S) :
    AlgebraicGeometry.Etale (atlasKernelPair_t X).left :=
  (relativeSpectrumAtlasPresentation X).isEtaleEquivalence.etale_t

/-- The atlas kernel-pair second projection is étale. -/
instance atlasKernelPair_s_etale (X : AlgebraicSpace S) :
    AlgebraicGeometry.Etale (atlasKernelPair_s X).left :=
  (relativeSpectrumAtlasPresentation X).isEtaleEquivalence.etale_s

/-- Both actual projections are open, as base changes of the étale atlas. -/
theorem atlasKernelPair_t_isOpenMap (X : AlgebraicSpace S) :
    IsOpenMap (atlasKernelPair_t X).left.base := by
  haveI : AlgebraicGeometry.Etale (atlasKernelPair_t X).left :=
    (atlasHom_presheaf_etale X).property (atlasHom X) _ _
      (relativeSpectrumAtlas_isPullback X).flip
  exact (atlasKernelPair_t X).left.isOpenMap

theorem atlasKernelPair_s_isOpenMap (X : AlgebraicSpace S) :
    IsOpenMap (atlasKernelPair_s X).left.base := by
  haveI : AlgebraicGeometry.Etale (atlasKernelPair_s X).left :=
    (atlasHom_presheaf_etale X).property (atlasHom X) _ _
      (relativeSpectrumAtlas_isPullback X)
  exact (atlasKernelPair_s X).left.isOpenMap

/-- The image of a kernel-pair open under an atlas kernel-pair projection. -/
def atlasKernelPairImage (X : AlgebraicSpace S) (φ : atlasKernelPair X ⟶ atlasScheme X)
    (hφ : IsOpenMap φ.left.base) (W : (atlasKernelPair X).left.Opens) : (atlasScheme X).left.Opens :=
  ⟨φ.left.base '' (W : Set _), hφ _ W.2⟩

/-- The carrier of `atlasKernelPairImage X φ hφ W` is the image of `W` under `φ`. -/
theorem atlasKernelPairImage_coe (X : AlgebraicSpace S)
    (φ : atlasKernelPair X ⟶ atlasScheme X) (hφ : IsOpenMap φ.left.base)
    (W : (atlasKernelPair X).left.Opens) :
    (atlasKernelPairImage X φ hφ W : Set _) = φ.left.base '' (W : Set _) :=
  rfl

/-- The morphism of schemes over `S` from a kernel-pair open to its image in the atlas. -/
def atlasKernelPairOpenOverHom (X : AlgebraicSpace S)
    (φ : atlasKernelPair X ⟶ atlasScheme X) (hφ : IsOpenMap φ.left.base)
    (W : (atlasKernelPair X).left.Opens) :
    kernelPairOpenOver X W ⟶ atlasOpenOver X (atlasKernelPairImage X φ hφ W) :=
  Over.homMk (φ.left.resLE (atlasKernelPairImage X φ hφ W) W (by
    intro x hx
    exact ⟨x, hx, rfl⟩)) (by
      change φ.left.resLE (atlasKernelPairImage X φ hφ W) W _ ≫
        ((atlasKernelPairImage X φ hφ W).ι ≫ (atlasScheme X).hom) =
        W.ι ≫ (atlasKernelPair X).hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w φ])

/-- The morphism of small étale objects over `X` from a kernel-pair open to its image in the
atlas. -/
def kernelPairOpenHom (X : AlgebraicSpace S) (φ : atlasKernelPair X ⟶ atlasScheme X)
    (hφ : IsOpenMap φ.left.base)
    (wφ : (ofOverFunctor S).map φ ≫ atlasHom X = atlasKernelPairHom X)
    (W : (atlasKernelPair X).left.Opens) :
    kernelPairOpenToSmallEtaleObj X W ⟶
      atlasOpenToSmallEtaleObj X (atlasKernelPairImage X φ hφ W) :=
  MorphismProperty.CostructuredArrow.homMk (atlasKernelPairOpenOverHom X φ hφ W) trivial (by
    have h : atlasKernelPairOpenOverHom X φ hφ W ≫
        atlasOpenOverHom X (atlasKernelPairImage X φ hφ W) = kernelPairOpenOverHom X W ≫ φ := by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.resLE_comp_ι _ _
    change yoneda.map (atlasKernelPairOpenOverHom X φ hφ W) ≫
      (yoneda.map (atlasOpenOverHom X (atlasKernelPairImage X φ hφ W)) ≫ atlasHom X) =
      yoneda.map (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X
    rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
    exact congrArg (fun f ↦ yoneda.map (kernelPairOpenOverHom X W) ≫ f) wφ)

/-- The underlying scheme morphism of `kernelPairOpenHom X φ hφ wφ W` is
`atlasKernelPairOpenOverHom X φ hφ W`. -/
theorem kernelPairOpenHom_left (X : AlgebraicSpace S)
    (φ : atlasKernelPair X ⟶ atlasScheme X) (hφ : IsOpenMap φ.left.base)
    (wφ : (ofOverFunctor S).map φ ≫ atlasHom X = atlasKernelPairHom X) (W : (atlasKernelPair X).left.Opens) :
    (kernelPairOpenHom X φ hφ wφ W).left = atlasKernelPairOpenOverHom X φ hφ W :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
