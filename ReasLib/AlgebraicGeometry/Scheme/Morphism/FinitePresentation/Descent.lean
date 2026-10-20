/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Restrict
import ReasLib.RingTheory.RingHom.FinitePresentation.FaithfullyFlat

/-!
# Descent of local finite presentation

This file records descent of local finite presentation under fppf precomposition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFinitePresentation

/-- Local finite presentation descends under precomposition by a surjective, flat, locally
finitely presented morphism. -/
instance hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := sorry

/-- In a commutative triangle `f ≫ q = p`, local finite presentation descends from `p` to `q`
when `f` is surjective, flat, and locally of finite presentation. -/
theorem of_comp_eq_of_fppf {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation p] (hcomm : f ≫ q = p) :
    LocallyOfFinitePresentation q := sorry

private theorem affine_of_comp_of_surjective_etale
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [IsAffine Y] [IsAffine S] [Surjective f] [Etale f]
    [LocallyOfFinitePresentation (f ≫ q)] : LocallyOfFinitePresentation q := by
  classical
  have hcover : (Set.univ : Set Y) ⊆ Set.range f := fun y _ ↦ f.surjective y
  obtain ⟨W : X.Opens, hW, hImage⟩ :=
    IsOpenMap.exists_opens_image_eq_of_prespectralSpace f.continuous f.isOpenMap
      hcover isOpen_univ isCompact_univ
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hW
  obtain ⟨Z, r, hr, hrLocal, hZ⟩ :=
    W.toScheme.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  letI : IsAffine Z := hZ
  letI : Surjective r := hr
  letI : IsLocalIso r := hrLocal
  letI : Etale r := IsLocalIso.le_of_isZariskiLocalAtSource @Etale _ _ r hrLocal
  haveI : Surjective (W.ι ≫ f) := by
    refine ⟨fun y ↦ ?_⟩
    have hy : y ∈ f '' (W : Set X) := hImage.symm ▸ Set.mem_univ y
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  let c : Z ⟶ Y := r ≫ W.ι ≫ f
  letI : Surjective c := by dsimp [c]; infer_instance
  letI : Etale c := by dsimp [c]; infer_instance
  letI : LocallyOfFinitePresentation (c ≫ q) := by
    simpa only [c, Category.assoc] using
      (inferInstance : LocallyOfFinitePresentation (r ≫ W.ι ≫ (f ≫ q)))
  have hcomp : (c.appTop.hom.comp q.appTop.hom).FinitePresentation := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      (Scheme.Hom.finitePresentation_appTop (c ≫ q))
  have hff : c.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f := c)).mp
      ⟨inferInstance, inferInstance⟩
  have het : c.appTop.hom.Etale := HasRingHomProperty.appTop @Etale c inferInstance
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr
    (RingHom.FinitePresentation.of_comp_of_faithfullyFlat_of_etale hcomp hff het)

/-- Local finite presentation descends from the displayed composite along a surjective étale
morphism. The finite affine refinement and its ring-map certificates are constructed from the
original cover and composite, retaining arbitrary coefficient schemes. -/
theorem of_comp_eq_of_surjective_etale
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] [Etale f] [LocallyOfFinitePresentation p] (hcomm : f ≫ q = p) :
    LocallyOfFinitePresentation q := by
  subst p
  constructor
  intro U hU V hV e
  letI : IsAffine U := hU
  letI : IsAffine V := hV
  let fV : (f ⁻¹ᵁ V).toScheme ⟶ V.toScheme := f ∣_ V
  let g : V.toScheme ⟶ U.toScheme := q.resLE U V e
  letI : Etale fV := by dsimp [fV]; infer_instance
  letI : Surjective fV :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance V
  letI : LocallyOfFinitePresentation (fV ≫ g) := by
    dsimp [fV, g]
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    infer_instance
  haveI : LocallyOfFinitePresentation g := affine_of_comp_of_surjective_etale fV g
  exact (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso q U V e)).mp (Scheme.Hom.finitePresentation_appTop g)

end AlgebraicGeometry.LocallyOfFinitePresentation
