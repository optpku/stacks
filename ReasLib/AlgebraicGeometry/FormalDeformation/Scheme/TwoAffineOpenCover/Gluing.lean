/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover.Restriction
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Gluing deformation categories along two affine opens

Restriction and global sections give the canonical comparison with the two-fibre
product of coordinate-ring deformation categories.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
/-- The two-fibre product of the coordinate-ring deformation categories over the overlap. -/
abbrev ringDeformationPullback :=
  BasedCategory.PseudoPullback (restrictRing₁ Λ k c hX) (restrictRing₂ Λ k c hX)

/-- The projection of the two-fibre product returns its stored Artinian base. -/
theorem ringDeformationPullback_p_obj
    (P : (ringDeformationPullback Λ k c hX).obj) :
    (ringDeformationPullback Λ k c hX).p.obj P =
      BasedCategory.PseudoPullback.baseObj P :=
  rfl

variable [AlgebraicGeometry.Flat hX]

private theorem gluingFlatSchemeHom_ext {Q P : FlatSchemeCat Λ k} (f g : Q ⟶ P)
    (hbase : f.baseHom = g.baseHom) (hscheme : f.schemeHom = g.schemeHom) : f = g := by
  cases f
  cases g
  cases hbase
  cases hscheme
  rfl

private theorem gluingFlatAlgebraHom_ext {Q P : FlatAlgebraCat Λ k} (f g : Q ⟶ P)
    (hbase : f.baseHom = g.baseHom) (hring : f.toRingHom = g.toRingHom) : f = g := by
  rcases f with ⟨_, _, _, _⟩
  rcases g with ⟨_, _, _, _⟩
  cases hbase
  cases hring
  rfl

omit [AlgebraicGeometry.Flat hX] in
private theorem gluing_specStructureHom_w (U : X.Opens) (hU : IsAffineOpen U) :
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (hX.sectionsMap U)) = U.ι ≫ hX := by
  change U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (hX.sectionsMap U)) = _
  rw [Scheme.Hom.sectionsMap, CommRingCat.ofHom_hom, Spec.map_comp,
    ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE, Scheme.Opens.toSpecΓ_top]
  simp only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  exact Scheme.Hom.resLE_comp_ι _ _

/-- The slice projection of `Def_X` to `C_Λ`. -/
abbrev schemeForget : FlatSchemeCat.deformationCategory Λ k X hX ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
    FlatSchemeCat.forget Λ k

/-- Transport a deformation of `U₁` along `U₁ ≅ Spec P₁`. -/
def transportSpec₁ (ξ : deformationCategory_U₁ Λ k c hX) :
    FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (ring₁ c)))
      (specStructureHom₁ Λ k c hX) :=
  Over.mk <|
    FlatSchemeCat.Hom.of ξ.hom.baseHom (c.isoSpec₁.inv ≫ ξ.hom.schemeHom) (by
      apply ξ.hom.isPullback.of_iso' c.isoSpec₁.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · exact (Category.comp_id _).symm
      · change c.isoSpec₁.inv ≫ (c.U₁.ι ≫ hX) = specStructureHom₁ Λ k c hX ≫ 𝟙 _
        rw [← gluing_specStructureHom_w Λ k hX c.U₁ c.isAffine_U₁]
        change c.isoSpec₁.inv ≫ (c.isoSpec₁.hom ≫ specStructureHom₁ Λ k c hX) = _
        simp
      · exact (Category.comp_id ξ.left.structureHom).trans
          (Category.id_comp ξ.left.structureHom).symm
      · exact (Category.id_comp (FlatSchemeCat.specMap ξ.hom.baseHom)).trans
          (Category.comp_id (FlatSchemeCat.specMap ξ.hom.baseHom)).symm)

/-- Transport a deformation of `U₂` along `U₂ ≅ Spec P₂`. -/
def transportSpec₂ (ξ : deformationCategory_U₂ Λ k c hX) :
    FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (ring₂ c)))
      (specStructureHom₂ Λ k c hX) :=
  Over.mk <|
    FlatSchemeCat.Hom.of ξ.hom.baseHom (c.isoSpec₂.inv ≫ ξ.hom.schemeHom) (by
      apply ξ.hom.isPullback.of_iso' c.isoSpec₂.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · exact (Category.comp_id _).symm
      · change c.isoSpec₂.inv ≫ (c.U₂.ι ≫ hX) = specStructureHom₂ Λ k c hX ≫ 𝟙 _
        rw [← gluing_specStructureHom_w Λ k hX c.U₂ c.isAffine_U₂]
        change c.isoSpec₂.inv ≫ (c.isoSpec₂.hom ≫ specStructureHom₂ Λ k c hX) = _
        simp
      · exact (Category.comp_id ξ.left.structureHom).trans
          (Category.id_comp ξ.left.structureHom).symm
      · exact (Category.id_comp (FlatSchemeCat.specMap ξ.hom.baseHom)).trans
          (Category.comp_id (FlatSchemeCat.specMap ξ.hom.baseHom)).symm)

/-- The deformation of `P₁` obtained by restricting `ξ` to `U₁` and taking global sections. -/
def glueFstObj (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : deformationCategory_ring₁ Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  (FlatSchemeCat.globalSectionsFunctor Λ k P).obj
    (transportSpec₁ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).obj ξ))

/-- The deformation of `P₂` obtained by restricting `ξ` to `U₂` and taking global sections. -/
def glueSndObj (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : deformationCategory_ring₂ Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  (FlatSchemeCat.globalSectionsFunctor Λ k P).obj
    (transportSpec₂ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).obj ξ))

/-- `glueFstObj` keeps the Artinian base of the original deformation. -/
theorem glueFstObj_left_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (glueFstObj Λ k c hX ξ).left.base = ξ.left.base :=
  rfl

/-- `glueSndObj` keeps the Artinian base of the original deformation. -/
theorem glueSndObj_left_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (glueSndObj Λ k c hX ξ).left.base = ξ.left.base :=
  rfl

/-- A morphism of deformations of `X` induces the corresponding morphism of `P₁`-deformations. -/
def glueFstMap {ξ η : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    glueFstObj Λ k c hX ξ ⟶ glueFstObj Λ k c hX η := by
  let src := transportSpec₁ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).obj ξ)
  let tgt := transportSpec₁ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).obj η)
  let base := φ.left.baseHom
  let map := (FlatSchemeCat.restrictMap Λ k X hX c.U₁ φ).schemeHom
  have certificates :
      IsPullback map tgt.left.structureHom src.left.structureHom (FlatSchemeCat.specMap base) ∧
      (∀ cartesian, FlatSchemeCat.Hom.of (src := src.left) (tgt := tgt.left) base map cartesian ≫
        tgt.hom = src.hom) := by
    refine ⟨(FlatSchemeCat.restrictMap Λ k X hX c.U₁ φ).isPullback, ?_⟩
    intro cartesian
    apply gluingFlatSchemeHom_ext
    · have hbase := congrArg FlatSchemeCat.Hom.baseHom
        (FlatSchemeCat.restrictMap_w Λ k X hX c.U₁ φ)
      exact hbase
    · exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ c.isoSpec₁.inv ≫ f.schemeHom)
          (FlatSchemeCat.restrictMap_w Λ k X hX c.U₁ φ))
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  exact (FlatSchemeCat.globalSectionsFunctor Λ k P).map
    (Over.homMk (FlatSchemeCat.Hom.of base map certificates.1) (certificates.2 certificates.1))

/-- A morphism of deformations of `X` induces the corresponding morphism of `P₂`-deformations. -/
def glueSndMap {ξ η : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    glueSndObj Λ k c hX ξ ⟶ glueSndObj Λ k c hX η := by
  let src := transportSpec₂ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).obj ξ)
  let tgt := transportSpec₂ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).obj η)
  let base := φ.left.baseHom
  let map := (FlatSchemeCat.restrictMap Λ k X hX c.U₂ φ).schemeHom
  have certificates :
      IsPullback map tgt.left.structureHom src.left.structureHom (FlatSchemeCat.specMap base) ∧
      (∀ cartesian, FlatSchemeCat.Hom.of (src := src.left) (tgt := tgt.left) base map cartesian ≫
        tgt.hom = src.hom) := by
    refine ⟨(FlatSchemeCat.restrictMap Λ k X hX c.U₂ φ).isPullback, ?_⟩
    intro cartesian
    apply gluingFlatSchemeHom_ext
    · have hbase := congrArg FlatSchemeCat.Hom.baseHom
        (FlatSchemeCat.restrictMap_w Λ k X hX c.U₂ φ)
      exact hbase
    · exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ c.isoSpec₂.inv ≫ f.schemeHom)
          (FlatSchemeCat.restrictMap_w Λ k X hX c.U₂ φ))
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  exact (FlatSchemeCat.globalSectionsFunctor Λ k P).map
    (Over.homMk (FlatSchemeCat.Hom.of base map certificates.1) (certificates.2 certificates.1))

private theorem gluingFstMap_id (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    glueFstMap Λ k c hX (𝟙 ξ) = 𝟙 (glueFstObj Λ k c hX ξ) := by
  apply Over.OverMorphism.ext
  apply gluingFlatAlgebraHom_ext
  · rfl
  · change (FlatSchemeCat.restrictMap Λ k X hX c.U₁ (𝟙 ξ)).schemeHom.appTop.hom =
      RingHom.id _
    have h := congrArg (fun f ↦ f.left.schemeHom)
      ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).map_id ξ)
    change (FlatSchemeCat.restrictMap Λ k X hX c.U₁ (𝟙 ξ)).schemeHom = 𝟙 _ at h
    rw [h, Scheme.Hom.id_appTop]
    rfl

private theorem gluingFstMap_comp {ξ η ζ : FlatSchemeCat.deformationCategory Λ k X hX}
    (φ : ξ ⟶ η) (ψ : η ⟶ ζ) :
    glueFstMap Λ k c hX (φ ≫ ψ) = glueFstMap Λ k c hX φ ≫ glueFstMap Λ k c hX ψ := by
  dsimp only [glueFstMap]
  erw [← Functor.map_comp]
  apply congrArg
  apply Over.OverMorphism.ext
  apply gluingFlatSchemeHom_ext
  · rfl
  · exact (Scheme.Hom.resLE_comp_resLE _ _ _ _).symm

private theorem gluingSndMap_id (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    glueSndMap Λ k c hX (𝟙 ξ) = 𝟙 (glueSndObj Λ k c hX ξ) := by
  apply Over.OverMorphism.ext
  apply gluingFlatAlgebraHom_ext
  · rfl
  · change (FlatSchemeCat.restrictMap Λ k X hX c.U₂ (𝟙 ξ)).schemeHom.appTop.hom =
      RingHom.id _
    have h := congrArg (fun f ↦ f.left.schemeHom)
      ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).map_id ξ)
    change (FlatSchemeCat.restrictMap Λ k X hX c.U₂ (𝟙 ξ)).schemeHom = 𝟙 _ at h
    rw [h, Scheme.Hom.id_appTop]
    rfl

private theorem gluingSndMap_comp {ξ η ζ : FlatSchemeCat.deformationCategory Λ k X hX}
    (φ : ξ ⟶ η) (ψ : η ⟶ ζ) :
    glueSndMap Λ k c hX (φ ≫ ψ) = glueSndMap Λ k c hX φ ≫ glueSndMap Λ k c hX ψ := by
  dsimp only [glueSndMap]
  erw [← Functor.map_comp]
  apply congrArg
  apply Over.OverMorphism.ext
  apply gluingFlatSchemeHom_ext
  · rfl
  · exact (Scheme.Hom.resLE_comp_resLE _ _ _ _).symm

/-- The first fibre component of the image of a deformation of `X`. -/
def glueFstFiber (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (algebraForget_ring₁ Λ k c hX).Fiber ξ.left.base :=
  Fiber.mk (a := glueFstObj Λ k c hX ξ) (glueFstObj_left_base Λ k c hX ξ)

/-- The second fibre component of the image of a deformation of `X`. -/
def glueSndFiber (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (algebraForget_ring₂ Λ k c hX).Fiber ξ.left.base :=
  Fiber.mk (a := glueSndObj Λ k c hX ξ) (glueSndObj_left_base Λ k c hX ξ)

/-- The corresponding open of `U₁` on a deformation of `X`. -/
abbrev correspondingOpen_U₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen c.U₁

/-- The corresponding open of `U₂` on a deformation of `X`. -/
abbrev correspondingOpen_U₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen c.U₂

/-- The corresponding open of `U₁ ⊓ U₂` on a deformation of `X`. -/
abbrev correspondingOpen_inf (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen (c.U₁ ⊓ c.U₂)

/-- The overlap open of a deformation of `X` is contained in the first chart open. -/
theorem correspondingOpen_inf_le_U₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    correspondingOpen_inf Λ k c hX ξ ≤ correspondingOpen_U₁ Λ k c hX ξ :=
  by
  exact Set.image_mono (SetLike.coe_mono (inf_le_left : c.U₁ ⊓ c.U₂ ≤ c.U₁))

/-- The overlap open of a deformation of `X` is contained in the second chart open. -/
theorem correspondingOpen_inf_le_U₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    correspondingOpen_inf Λ k c hX ξ ≤ correspondingOpen_U₂ Λ k c hX ξ :=
  by
  exact Set.image_mono (SetLike.coe_mono (inf_le_right : c.U₁ ⊓ c.U₂ ≤ c.U₂))

/-- Infinitesimal thickenings of affine opens remain affine. -/
theorem isAffine_correspondingOpen_U₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsAffine (correspondingOpen_U₁ Λ k c hX ξ).toScheme :=
  sorry

/-- Infinitesimal thickenings of affine opens remain affine. -/
theorem isAffine_correspondingOpen_U₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsAffine (correspondingOpen_U₂ Λ k c hX ξ).toScheme :=
  sorry

/-- The open of `Spec Γ(U₁_Y, ⊤)` corresponding to the affine overlap. -/
def glueFstOverlapOpen (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (Spec (CommRingCat.of (glueFstObj Λ k c hX ξ).left.algebra)).Opens :=
  ((specFunctor₁ Λ k c hX).obj (glueFstObj Λ k c hX ξ)).hom.correspondingOpen
    (overlapOpenSpec₁ c)

/-- The open of `Spec Γ(U₂_Y, ⊤)` corresponding to the affine overlap. -/
def glueSndOverlapOpen (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (Spec (CommRingCat.of (glueSndObj Λ k c hX ξ).left.algebra)).Opens :=
  ((specFunctor₂ Λ k c hX).obj (glueSndObj Λ k c hX ξ)).hom.correspondingOpen
    (overlapOpenSpec₂ c)

/-- Canonical map `Spec Γ(U₁_Y, ⊤) ⟶ Spec (Γ(U₁_Y, ⊤) : Type u)`. -/
private def specΓToSpecAlgebra₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Spec Γ((correspondingOpen_U₁ Λ k c hX ξ).toScheme, ⊤) ⟶
      Spec (CommRingCat.of (glueFstObj Λ k c hX ξ).left.algebra) :=
  Spec.map (CommRingCat.ofHom (RingHom.id _))

/-- Canonical map `Spec Γ(U₂_Y, ⊤) ⟶ Spec (Γ(U₂_Y, ⊤) : Type u)`. -/
private def specΓToSpecAlgebra₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Spec Γ((correspondingOpen_U₂ Λ k c hX ξ).toScheme, ⊤) ⟶
      Spec (CommRingCat.of (glueSndObj Λ k c hX ξ).left.algebra) :=
  Spec.map (CommRingCat.ofHom (RingHom.id _))

private theorem gluing_restricted_range (ξ : FlatSchemeCat.deformationCategory Λ k X hX)
    {U V : X.Opens} (hVU : V ≤ U) (e : U.toScheme ≅ Spec Γ(X, U))
    {S : Scheme.{u}} (a : (ξ.hom.correspondingOpen U).toScheme ⟶ S) :
    Set.range (ξ.left.scheme.homOfLE
      (show ξ.hom.correspondingOpen V ≤ ξ.hom.correspondingOpen U from
        Set.image_mono (SetLike.coe_mono hVU)) ≫ a) =
      (e.inv ≫ (FlatSchemeCat.restrictHom Λ k X hX U ξ).schemeHom ≫ a) ''
        ((e.inv ≫ U.ι) ⁻¹' (V : Set X)) := by
  let i : (ξ.hom.correspondingOpen V).toScheme ⟶
      (ξ.hom.correspondingOpen U).toScheme := ξ.left.scheme.homOfLE
      (show ξ.hom.correspondingOpen V ≤ ξ.hom.correspondingOpen U from
        Set.image_mono (SetLike.coe_mono hVU))
  let r : U.toScheme ⟶ (ξ.hom.correspondingOpen U).toScheme :=
    (FlatSchemeCat.restrictHom Λ k X hX U ξ).schemeHom
  have hrange : Set.range i = r '' (U.ι ⁻¹' (V : Set X)) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx, hxz⟩ := z.2
      refine ⟨⟨x, hVU hx⟩, hx, ?_⟩
      apply Subtype.ext
      have hr : (r ⟨x, hVU hx⟩).1 = ξ.hom.schemeHom x :=
        Scheme.Hom.coe_resLE_apply _ _ _
      have hi : (i z).1 = z.1 := Scheme.homOfLE_apply _ _
      exact hr.trans (hxz.trans hi.symm)
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨ξ.hom.schemeHom x.1, ⟨x.1, hx, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      exact (Scheme.homOfLE_apply _ _).trans
        (Scheme.Hom.coe_resLE_apply _ _ x).symm
  change Set.range ((a : _ → _) ∘ (i : _ → _)) =
    (((a : _ → _) ∘ (r : _ → _)) ∘ (e.inv : _ → _)) ''
      ((e.inv : _ → _) ⁻¹' (U.ι ⁻¹' (V : Set X)))
  have himage : (e.inv : _ → _) ''
      ((e.inv : _ → _) ⁻¹' (U.ι ⁻¹' (V : Set X))) = U.ι ⁻¹' (V : Set X) :=
    Set.image_preimage_eq _ (ConcreteCategory.bijective_of_isIso e.inv.base).surjective
  calc
    Set.range ((a : _ → _) ∘ (i : _ → _)) = (a : _ → _) '' Set.range i :=
      Set.range_comp _ _
    _ = (a : _ → _) '' (r : _ → _) '' (U.ι ⁻¹' (V : Set X)) :=
      congrArg (Set.image (a : _ → _)) hrange
    _ = ((a : _ → _) ∘ (r : _ → _)) '' (U.ι ⁻¹' (V : Set X)) :=
      (Set.image_comp _ _ _).symm
    _ = _ := (congrArg (Set.image ((a : _ → _) ∘ (r : _ → _))) himage.symm).trans
      (Set.image_comp _ _ _).symm

/-- `U₁₂_Y ⟶ Spec (Γ(U₁_Y, ⊤) : Type u)` is an open immersion. -/
theorem isOpenImmersion_overlapToSpecAlgebra₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsOpenImmersion
      (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₁ Λ k c hX ξ) ≫
        (correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₁ Λ k c hX ξ) := by
  letI := isAffine_correspondingOpen_U₁ Λ k c hX ξ
  haveI : IsIso (specΓToSpecAlgebra₁ Λ k c hX ξ) := by
    change IsIso (Spec.map (𝟙 Γ((correspondingOpen_U₁ Λ k c hX ξ).toScheme, ⊤)))
    infer_instance
  infer_instance

/-- `U₁₂_Y ⟶ Spec (Γ(U₂_Y, ⊤) : Type u)` is an open immersion. -/
theorem isOpenImmersion_overlapToSpecAlgebra₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsOpenImmersion
      (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₂ Λ k c hX ξ) ≫
        (correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₂ Λ k c hX ξ) := by
  letI := isAffine_correspondingOpen_U₂ Λ k c hX ξ
  haveI : IsIso (specΓToSpecAlgebra₂ Λ k c hX ξ) := by
    change IsIso (Spec.map (𝟙 Γ((correspondingOpen_U₂ Λ k c hX ξ).toScheme, ⊤)))
    infer_instance
  infer_instance

/-- Scheme isomorphism `U₁₂_Y ≅ W₁` of corresponding overlap opens. -/
def glueingOverlapIso₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (correspondingOpen_inf Λ k c hX ξ).toScheme ≅
      (glueFstOverlapOpen Λ k c hX ξ).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₁ Λ k c hX ξ) ≫
      (correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
        specΓToSpecAlgebra₁ Λ k c hX ξ)
    (glueFstOverlapOpen Λ k c hX ξ).ι
    (isOpenImmersion_overlapToSpecAlgebra₁ Λ k c hX ξ) inferInstance <| by
      have hid : specΓToSpecAlgebra₁ Λ k c hX ξ = 𝟙 _ := by
        change Spec.map (𝟙 Γ((correspondingOpen_U₁ Λ k c hX ξ).toScheme, ⊤)) = 𝟙 _
        exact Spec.map_id _
      have hspec :
          ((specFunctor₁ Λ k c hX).obj (glueFstObj Λ k c hX ξ)).hom.schemeHom =
            c.isoSpec₁.inv ≫ (FlatSchemeCat.restrictHom Λ k X hX c.U₁ ξ).schemeHom ≫
              (correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
                specΓToSpecAlgebra₁ Λ k c hX ξ := by
        erw [hid, Category.comp_id]
        change Spec.map ((c.isoSpec₁.inv ≫
          (FlatSchemeCat.restrictHom Λ k X hX c.U₁ ξ).schemeHom).appTop ≫
            (Scheme.ΓSpecIso Γ(X, c.U₁)).hom) = _
        rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Scheme.toSpecΓ_naturality]
        rfl
      rw [Scheme.Opens.range_ι]
      change Set.range
          (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₁ Λ k c hX ξ) ≫
            ((correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
              specΓToSpecAlgebra₁ Λ k c hX ξ)) =
        ((specFunctor₁ Λ k c hX).obj (glueFstObj Λ k c hX ξ)).hom.schemeHom ''
          (c.fromSpec₁ ⁻¹' (c.U₁ ⊓ c.U₂ : Set X))
      erw [hspec]
      exact gluing_restricted_range Λ k hX ξ inf_le_left c.isoSpec₁
        ((correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₁ Λ k c hX ξ)

/-- Scheme isomorphism `U₁₂_Y ≅ W₂` of corresponding overlap opens. -/
def glueingOverlapIso₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (correspondingOpen_inf Λ k c hX ξ).toScheme ≅
      (glueSndOverlapOpen Λ k c hX ξ).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₂ Λ k c hX ξ) ≫
      (correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
        specΓToSpecAlgebra₂ Λ k c hX ξ)
    (glueSndOverlapOpen Λ k c hX ξ).ι
    (isOpenImmersion_overlapToSpecAlgebra₂ Λ k c hX ξ) inferInstance <| by
      have hid : specΓToSpecAlgebra₂ Λ k c hX ξ = 𝟙 _ := by
        change Spec.map (𝟙 Γ((correspondingOpen_U₂ Λ k c hX ξ).toScheme, ⊤)) = 𝟙 _
        exact Spec.map_id _
      have hspec :
          ((specFunctor₂ Λ k c hX).obj (glueSndObj Λ k c hX ξ)).hom.schemeHom =
            c.isoSpec₂.inv ≫ (FlatSchemeCat.restrictHom Λ k X hX c.U₂ ξ).schemeHom ≫
              (correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
                specΓToSpecAlgebra₂ Λ k c hX ξ := by
        erw [hid, Category.comp_id]
        change Spec.map ((c.isoSpec₂.inv ≫
          (FlatSchemeCat.restrictHom Λ k X hX c.U₂ ξ).schemeHom).appTop ≫
            (Scheme.ΓSpecIso Γ(X, c.U₂)).hom) = _
        rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Scheme.toSpecΓ_naturality]
        rfl
      rw [Scheme.Opens.range_ι]
      change Set.range
          (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₂ Λ k c hX ξ) ≫
            ((correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
              specΓToSpecAlgebra₂ Λ k c hX ξ)) =
        ((specFunctor₂ Λ k c hX).obj (glueSndObj Λ k c hX ξ)).hom.schemeHom ''
          (c.fromSpec₂ ⁻¹' (c.U₁ ⊓ c.U₂ : Set X))
      erw [hspec]
      exact gluing_restricted_range Λ k hX ξ inf_le_right c.isoSpec₂
        ((correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₂ Λ k c hX ξ)

/-- Scheme isomorphism of the two Spec-overlap opens of a deformation of `X`. -/
private def glueingOverlapSchemeIso (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (glueFstOverlapOpen Λ k c hX ξ).toScheme ≅
      (glueSndOverlapOpen Λ k c hX ξ).toScheme :=
  (glueingOverlapIso₁ Λ k c hX ξ).symm ≪≫ glueingOverlapIso₂ Λ k c hX ξ

/-- Global-sections ring map `Γ(W₁, ⊤) →+* Γ(W₂, ⊤)` of the overlap comparison. -/
private def glueingComparisonRingHom (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Γ((glueFstOverlapOpen Λ k c hX ξ).toScheme, ⊤) →+*
      Γ((glueSndOverlapOpen Λ k c hX ξ).toScheme, ⊤) :=
  (glueingOverlapSchemeIso Λ k c hX ξ).inv.appTop.hom

/-- Inverse global-sections ring map `Γ(W₂, ⊤) →+* Γ(W₁, ⊤)` of the overlap comparison. -/
private def glueingComparisonRingHom_inv (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Γ((glueSndOverlapOpen Λ k c hX ξ).toScheme, ⊤) →+*
      Γ((glueFstOverlapOpen Λ k c hX ξ).toScheme, ⊤) :=
  (glueingOverlapSchemeIso Λ k c hX ξ).hom.appTop.hom

/-- The first restricted ring deformation keeps the Artinian base of `ξ`. -/
theorem glueingComparison_fst_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left.base = ξ.left.base :=
  (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueFstFiber Λ k c hX ξ)).2

/-- The second restricted ring deformation keeps the Artinian base of `ξ`. -/
theorem glueingComparison_snd_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left.base = ξ.left.base :=
  (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueSndFiber Λ k c hX ξ)).2

/-- Forward morphism of restricted overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraHom (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left ⟶
      (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left := by
  let Q := (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueFstFiber Λ k c hX ξ)).1.left
  let P := (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueSndFiber Λ k c hX ξ)).1.left
  let base : Q.base ⟶ P.base := eqToHom ((glueingComparison_fst_base Λ k c hX ξ).trans
    (glueingComparison_snd_base Λ k c hX ξ).symm)
  let ring : Q.algebra →+* P.algebra := glueingComparisonRingHom Λ k c hX ξ
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- Inverse morphism of restricted overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraInv (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left ⟶
      (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left := by
  let Q := (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueSndFiber Λ k c hX ξ)).1.left
  let P := (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueFstFiber Λ k c hX ξ)).1.left
  let base : Q.base ⟶ P.base := eqToHom ((glueingComparison_snd_base Λ k c hX ξ).trans
    (glueingComparison_fst_base Λ k c hX ξ).symm)
  let ring : Q.algebra →+* P.algebra := glueingComparisonRingHom_inv Λ k c hX ξ
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- Ambient isomorphism of overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraIso (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left ≅
      (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left := by
  let hom := glueingComparisonAlgebraHom Λ k c hX ξ
  let inv := glueingComparisonAlgebraInv Λ k c hX ξ
  have certificates : (hom ≫ inv = 𝟙 _) ∧ (inv ≫ hom = 𝟙 _) := by
    constructor
    · apply gluingFlatAlgebraHom_ext
      · change eqToHom ((glueingComparison_fst_base Λ k c hX ξ).trans
            (glueingComparison_snd_base Λ k c hX ξ).symm) ≫
          eqToHom ((glueingComparison_snd_base Λ k c hX ξ).trans
            (glueingComparison_fst_base Λ k c hX ξ).symm) = 𝟙 _
        simp
      · have h : (glueingOverlapSchemeIso Λ k c hX ξ).inv.appTop ≫
            (glueingOverlapSchemeIso Λ k c hX ξ).hom.appTop = 𝟙 _ := by
          rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
        exact congrArg CommRingCat.Hom.hom h
    · apply gluingFlatAlgebraHom_ext
      · change eqToHom ((glueingComparison_snd_base Λ k c hX ξ).trans
            (glueingComparison_fst_base Λ k c hX ξ).symm) ≫
          eqToHom ((glueingComparison_fst_base Λ k c hX ξ).trans
            (glueingComparison_snd_base Λ k c hX ξ).symm) = 𝟙 _
        simp
      · have h : (glueingOverlapSchemeIso Λ k c hX ξ).hom.appTop ≫
            (glueingOverlapSchemeIso Λ k c hX ξ).inv.appTop = 𝟙 _ := by
          rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
        exact congrArg CommRingCat.Hom.hom h
  exact { hom := hom, inv := inv, hom_inv_id := certificates.1, inv_hom_id := certificates.2 }

/-- Comparison isomorphism in `Def_{P₁₂}` between the two restricted ring deformations. -/
def glueingComparisonIso (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    ((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj (glueFstFiber Λ k c hX ξ) ≅
      ((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj (glueSndFiber Λ k c hX ξ) := by
  let src := ((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj (glueFstFiber Λ k c hX ξ)
  let tgt := ((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj (glueSndFiber Λ k c hX ξ)
  let e := glueingComparisonAlgebraIso Λ k c hX ξ
  have certificates :
      (e.hom ≫ tgt.1.hom = src.1.hom) ∧
      (∀ compatible : e.hom ≫ tgt.1.hom = src.1.hom,
        (algebraForget_ringInf Λ k c hX).IsHomLift (𝟙 ξ.left.base)
          (Over.isoMk e compatible).hom) := sorry
  exact Functor.Fiber.isoMk (Over.isoMk e certificates.1) (certificates.2 certificates.1)

/-- The image of a deformation of `X` in the 2-fiber product of ring deformation categories. -/
def glueingObj (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (ringDeformationPullback Λ k c hX).obj :=
  BasedCategory.PseudoPullback.mk (restrictRing₁ Λ k c hX) (restrictRing₂ Λ k c hX) ξ.left.base
    { fst := glueFstFiber Λ k c hX ξ
      snd := glueSndFiber Λ k c hX ξ
      iso := glueingComparisonIso Λ k c hX ξ }

/-- A morphism of deformations of `X` induces a morphism of 2-fiber product objects. -/
def glueingMap {ξ η : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    glueingObj Λ k c hX ξ ⟶ glueingObj Λ k c hX η := by
  let base := (schemeForget Λ k hX).map φ
  let fst := glueFstMap Λ k c hX φ
  let snd := glueSndMap Λ k c hX φ
  have certificates :
      (algebraForget_ring₁ Λ k c hX).IsHomLift base fst ∧
      (algebraForget_ring₂ Λ k c hX).IsHomLift base snd ∧
      CommSq ((restrictRing₁ Λ k c hX).toFunctor.map fst)
        (BasedCategory.PseudoPullback.comparison (glueingObj Λ k c hX ξ))
        (BasedCategory.PseudoPullback.comparison (glueingObj Λ k c hX η))
        ((restrictRing₂ Λ k c hX).toFunctor.map snd) := sorry
  exact BasedCategory.PseudoPullback.Hom.mk base fst certificates.1 snd
    certificates.2.1 certificates.2.2

/-- The ordinary functor `Def_X ⥤ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`. -/
def glueingFunctor :
    FlatSchemeCat.deformationCategory Λ k X hX ⥤ (ringDeformationPullback Λ k c hX).obj := by
  have certificates :
      (∀ ξ : FlatSchemeCat.deformationCategory Λ k X hX,
        glueingMap Λ k c hX (𝟙 ξ) = 𝟙 (glueingObj Λ k c hX ξ)) ∧
      (∀ {ξ η ζ : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) (ψ : η ⟶ ζ),
        glueingMap Λ k c hX (φ ≫ ψ) = glueingMap Λ k c hX φ ≫ glueingMap Λ k c hX ψ) := by
    constructor
    · intro ξ
      apply BasedCategory.PseudoPullback.hom_ext
      · exact gluingFstMap_id Λ k c hX ξ
      · exact gluingSndMap_id Λ k c hX ξ
    · intro ξ η ζ φ ψ
      apply BasedCategory.PseudoPullback.hom_ext
      · exact gluingFstMap_comp Λ k c hX φ ψ
      · exact gluingSndMap_comp Λ k c hX φ ψ
  exact {
    obj := glueingObj Λ k c hX
    map := glueingMap Λ k c hX
    map_id := certificates.1
    map_comp := certificates.2 }

/-- `glueingFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem glueingFunctor_comp_forget :
    (glueingFunctor Λ k c hX).comp (ringDeformationPullback Λ k c hX).p =
      schemeForget Λ k hX := by
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ f ↦
    ((Category.id_comp (f.left.baseHom ≫ 𝟙 _)).trans
      (Category.comp_id f.left.baseHom)).symm)

/-- The based functor `Def_X ⥤ᵇ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`. -/
def glueingBasedFunctor :
    BasedCategory.ofFunctor (schemeForget Λ k hX) ⥤ᵇ ringDeformationPullback Λ k c hX where
  toFunctor := glueingFunctor Λ k c hX
  w := glueingFunctor_comp_forget Λ k c hX

/-- The underlying ordinary functor of `glueingBasedFunctor` is `glueingFunctor`. -/
theorem glueingBasedFunctor_toFunctor :
    (glueingBasedFunctor Λ k c hX).toFunctor = glueingFunctor Λ k c hX :=
  rfl

/-- Restriction to a two-chart affine cover and global sections induce an equivalence
of deformation categories over the Artinian local algebra base. -/
theorem glueingBasedFunctor_isEquivalence :
    BasedFunctor.IsEquivalence (glueingBasedFunctor Λ k c hX) :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
