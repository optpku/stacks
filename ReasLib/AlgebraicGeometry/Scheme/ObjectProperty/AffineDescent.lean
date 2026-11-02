/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AffineScheme.StandardMorphisms
public import ReasLib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.StandardRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic.StandardRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ObjectProperty

open AlgebraicGeometry.Scheme

variable (P : CategoryTheory.ObjectProperty Scheme.{u})

private lemma of_openImmersion [P.IsLocal Scheme.zariskiPrecoverage]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (hY : P Y) : P X :=
  (P.iff_of_zeroHypercover (Y.affineCover.add f)).mp hY none

private lemma of_affineTarget [P.IsLocal Scheme.zariskiPrecoverage]
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource Q]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (Q.inverseImage AffineScheme.forgetToScheme)]
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) (hf : Q f) (hY : P Y) : P X := by
  apply P.of_zeroHypercover X.affineCover
  intro i
  exact (P.inverseImage AffineScheme.forgetToScheme).of_hom_of_target
    (Q := Q.inverseImage AffineScheme.forgetToScheme)
    (AffineScheme.ofHom (X.affineCover.f i ≫ f))
    (IsZariskiLocalAtSource.comp hf (X.affineCover.f i)) hY

private lemma of_hom_of_affine [P.IsLocal Scheme.zariskiPrecoverage]
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource Q]
    [Q.IsStableUnderBaseChange]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (Q.inverseImage AffineScheme.forgetToScheme)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Q f) (hY : P Y) : P X := by
  apply P.of_zeroHypercover (Y.affineCover.pullback₁ f)
  intro i
  exact of_affineTarget P Q (pullback.snd f (Y.affineCover.f i))
    (Q.pullback_snd _ _ hf) ((P.iff_of_zeroHypercover Y.affineCover).mp hY i)

/-- Finite affine refinements reduce quasi-compact descent to a single surjective
morphism between affine schemes, by taking the finite coproduct of the charts. -/
private lemma isLocal_propQC_of_affine [P.IsLocal Scheme.zariskiPrecoverage]
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource Q]
    [Q.IsStableUnderBaseChange]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (Q.inverseImage AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      ((Q ⊓ @Surjective).inverseImage AffineScheme.forgetToScheme)] :
    P.IsLocal (Scheme.propQCPrecoverage Q) := by
  apply CategoryTheory.ObjectProperty.IsLocal.mk_of_zeroHypercover
  intro X 𝒰
  constructor
  · intro h i
    exact of_hom_of_affine P Q ((Scheme.Cover.forgetQc 𝒰).f i)
      ((Scheme.Cover.forgetQc 𝒰).map_prop i) h
  · intro h
    apply P.of_zeroHypercover X.affineCover
    intro i
    let 𝒱 := Scheme.Cover.forgetQc (𝒰.pullback₂ (X.affineCover.f i))
    have h𝒱 (j : 𝒱.I₀) : P (𝒱.X j) := by
      exact @of_openImmersion P _ _ _ (pullback.fst (𝒰.f j) (X.affineCover.f i))
        (MorphismProperty.pullback_fst _ _ (X.affineCover.map_prop i)) (h j)
    obtain ⟨𝒲, φ, hfin, hφ⟩ :
        ∃ (𝒲 : (X.affineCover.X i).AffineCover.{u + 1} Q) (φ : 𝒲.cover ⟶ 𝒱),
          Finite 𝒲.I₀ ∧ ∀ j, IsOpenImmersion (φ.h₀ j) :=
      QuasiCompactCover.exists_hom 𝒱
    letI : Finite 𝒲.cover.I₀ := hfin
    have hsource : P (∐ 𝒲.cover.X) := by
      apply P.of_zeroHypercover (sigmaOpenCover 𝒲.cover.X)
      intro j
      exact @of_openImmersion P _ _ _ (φ.h₀ j) (hφ j) (h𝒱 (φ.s₀ j))
    apply (P.inverseImage AffineScheme.forgetToScheme).of_hom_of_source
      (Q := (Q ⊓ @Surjective).inverseImage AffineScheme.forgetToScheme)
      (AffineScheme.ofHom (Sigma.desc 𝒲.cover.f)) ?_ hsource
    refine ⟨IsZariskiLocalAtSource.sigmaDesc 𝒲.cover.map_prop, ⟨?_⟩⟩
    intro y
    obtain ⟨j, x, rfl⟩ := 𝒲.cover.exists_eq y
    refine ⟨Sigma.ι 𝒲.cover.X j x, ?_⟩
    change (Sigma.desc 𝒲.cover.f) ((Sigma.ι 𝒲.cover.X j) x) = (𝒲.cover.f j) x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]

private lemma isLocal_precoverage_of_affine [P.IsLocal Scheme.zariskiPrecoverage]
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource Q]
    [Q.IsStableUnderBaseChange]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (Q.inverseImage AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      ((Q ⊓ @Surjective).inverseImage AffineScheme.forgetToScheme)]
    (hopen : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), Q f → IsOpenMap f) :
    P.IsLocal (Scheme.precoverage Q) := by
  letI := isLocal_propQC_of_affine P Q
  apply CategoryTheory.ObjectProperty.IsLocal.of_le (L := Scheme.propQCPrecoverage Q)
  exact le_inf (Scheme.precoverage_le_qcPrecoverage_of_isOpenMap hopen) le_rfl

/-- Shrinking the open image of a local affine chart gives surjective affine charts. -/
private lemma of_surjective_of_affine_charts [P.IsLocal Scheme.zariskiPrecoverage]
    (R : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
    (hRiso : RingHom.RespectsIso R) (hRbase : RingHom.IsStableUnderBaseChange R)
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource Q]
    [IsZariskiLocalAtTarget Q]
    (hopen : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), Q f → IsOpenMap f)
    (hcharts : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), Q f → ∀ x : X,
      ∃ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
        (_ : x ∈ U) (e : U ≤ f ⁻¹ᵁ V), R (f.appLE V U e).hom)
    (hdesc : ∀ ⦃X Y : Scheme.{u}⦄ [IsAffine X] [IsAffine Y] (f : X ⟶ Y),
      R f.appTop.hom → Surjective f → P X → P Y)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Q f) (hs : Surjective f) (hX : P X) : P Y := by
  classical
  letI : Surjective f := hs
  letI : (RingHom.toMorphismProperty R).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hRiso
  have H (y : Y) : ∃ (Z : Scheme.{u}) (g : Z ⟶ Y),
      IsOpenImmersion g ∧ P Z ∧ y ∈ Set.range g := by
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨V, hV, U, hU, hx, e, hR⟩ := hcharts f hf x
    letI : IsAffine U.toScheme := hU
    letI : IsAffine V.toScheme := hV
    let g := f.resLE V U e
    have hgR : R g.appTop.hom :=
      (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty R)
        (arrowResLEAppIso f V U e)).mpr hR
    have hgQ : Q g := IsZariskiLocalAtSource.resLE e hf
    let O : V.toScheme.Opens := ⟨Set.range g, (hopen g hgQ).isOpen_range⟩
    obtain ⟨(W : V.toScheme.Opens), hW, hyW, hWO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      V.toScheme.isBasis_affineOpens (show g ⟨x, hx⟩ ∈ O from ⟨⟨x, hx⟩, rfl⟩)
    letI : IsAffine W.toScheme := hW
    have hsur : Surjective (pullback.fst W.ι g) := by
      constructor
      intro z
      obtain ⟨w, hw⟩ := hWO z.property
      obtain ⟨t, ht, _⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := W.ι) (g := g) z w hw.symm
      exact ⟨t, ht⟩
    have hsource : P (pullback W.ι g) :=
      @of_openImmersion P _ _ _ (pullback.snd W.ι g)
        (MorphismProperty.pullback_snd _ _ (inferInstance : IsOpenImmersion W.ι))
        (of_openImmersion P U.ι hX)
    have htarget : P W.toScheme := hdesc (pullback.fst W.ι g)
      (RingHom.IsStableUnderBaseChange.pullback_fst_appTop R hRbase hRiso W.ι g hgR)
      hsur hsource
    refine ⟨W.toScheme, W.ι ≫ V.ι, inferInstance, htarget, ⟨⟨g ⟨x, hx⟩, hyW⟩, ?_⟩⟩
    change (g ≫ V.ι) ⟨x, hx⟩ = f x
    dsimp only [g]
    rw [Scheme.Hom.resLE_comp_ι]
    rfl
  choose Z g hg hP hy using H
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y Z g (fun y ↦ ⟨y, hy y⟩) hg
  exact P.of_zeroHypercover 𝒰 hP

/-- A Zariski-local property that ascends along flat morphisms of affine schemes and
descends along surjective flat morphisms of affine schemes is fpqc-local. -/
instance fpqcLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.fpqcPrecoverage :=
  isLocal_propQC_of_affine P (@Flat)

/-- A Zariski-local property that ascends along flat, locally finitely presented morphisms
of affine schemes and descends along their surjective members is fppf-local. -/
instance fppfLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective) : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.fppfPrecoverage := by
  apply isLocal_precoverage_of_affine P (@Flat ⊓ @LocallyOfFinitePresentation)
  intro X Y f hf
  letI : Flat f := hf.1
  letI : LocallyOfFinitePresentation f := hf.2
  exact f.isOpenMap

/-- A Zariski-local property that ascends along étale morphisms of affine schemes and
descends along surjective étale morphisms of affine schemes is étale-local. -/
instance etaleLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Etale ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.etalePrecoverage := by
  apply isLocal_precoverage_of_affine P (@Etale)
  intro X Y f hf
  letI : Etale f := hf
  exact f.isOpenMap

/-- A Zariski-local property that ascends along smooth morphisms of affine schemes and
descends along surjective smooth morphisms of affine schemes is smooth-local. -/
instance smoothLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Smooth ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSmoothPrecoverage := by
  apply isLocal_precoverage_of_affine P (@Smooth)
  intro X Y f hf
  letI : Smooth f := hf
  exact f.isOpenMap

/-- A Zariski-local property that ascends along syntomic morphisms of affine schemes and
descends along surjective syntomic morphisms of affine schemes is syntomic-local. -/
instance syntomicLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Syntomic ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSyntomicPrecoverage := sorry

/-- A Zariski-local property that ascends along smooth morphisms of affine schemes and
descends along surjective standard smooth morphisms of affine schemes is smooth-local. -/
instance standardSmoothLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardSmooth ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSmoothPrecoverage := by
  have hopen ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) (hf : Smooth f) : IsOpenMap f := by
    letI : Smooth f := hf
    exact f.isOpenMap
  have hcharts ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) (hf : Smooth f) (x : X) :
      ∃ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
        (_ : x ∈ U) (e : U ≤ f ⁻¹ᵁ V), RingHom.IsStandardSmooth (f.appLE V U e).hom := by
    letI : Smooth f := hf
    exact Smooth.exists_isStandardSmooth f x
  have hdesc ⦃X Y : Scheme.{u}⦄ [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
      (hf : RingHom.IsStandardSmooth f.appTop.hom) (hs : Surjective f) (hX : P X) : P Y :=
    (P.inverseImage AffineScheme.forgetToScheme).of_hom_of_source
      (Q := AffineScheme.standardSmooth ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)
      (AffineScheme.ofHom f) ⟨hf, hs⟩ hX
  letI : (P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Smooth ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme) := {
    of_hom_of_source f hf hX :=
      of_surjective_of_affine_charts P (@RingHom.IsStandardSmooth)
        RingHom.isStandardSmooth_respectsIso RingHom.isStandardSmooth_isStableUnderBaseChange
        (@Smooth) hopen hcharts hdesc (AffineScheme.forgetToScheme.map f) hf.1 hf.2 hX }
  exact AlgebraicGeometry.Scheme.ObjectProperty.smoothLocalOfZariskiLocal P

/-- A Zariski-local property that ascends along syntomic morphisms of affine schemes and
descends along surjective standard syntomic morphisms of affine schemes is syntomic-local. -/
instance standardSyntomicLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardSyntomic ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSyntomicPrecoverage := sorry

/-- A Zariski-local property that ascends along étale morphisms of affine schemes and
descends along surjective standard étale morphisms of affine schemes is étale-local. -/
instance standardEtaleLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardEtale ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.etalePrecoverage := by
  let R : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop :=
    fun {_ _} _ _ f ↦ @Algebra.IsStandardEtale _ _ _ _ f.toAlgebra
  have hRiso : RingHom.RespectsIso R := by
    constructor
    · intro A B C _ _ _ f e hf
      letI : Algebra A B := f.toAlgebra
      letI : Algebra A C := (e.toRingHom.comp f).toAlgebra
      letI : Algebra.IsStandardEtale A B := hf
      exact Algebra.IsStandardEtale.of_equiv
        ({ e with commutes' := fun _ ↦ rfl } : B ≃ₐ[A] C)
    · intro A B C _ _ _ f e hf
      letI : Algebra B C := f.toAlgebra
      letI : Algebra B A := e.symm.toRingHom.toAlgebra
      letI : Algebra A C := (f.comp e.toRingHom).toAlgebra
      letI : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq' (by
        ext x
        change f x = f (e (e.symm x))
        rw [e.apply_symm_apply])
      letI : Algebra.IsStandardEtale B C := hf
      letI : Algebra.IsPushout B C A C := Algebra.IsPushout.of_bijective_left A C e.symm.bijective
      letI : Algebra.IsPushout B A C C := Algebra.IsPushout.symm inferInstance
      exact Algebra.IsStandardEtale.of_equiv (Algebra.IsPushout.equiv B A C C)
  have hRbase : RingHom.IsStableUnderBaseChange R := by
    apply RingHom.IsStableUnderBaseChange.mk hRiso
    intro A B C _ _ _ _ _ hf
    dsimp only [R] at hf ⊢
    replace hf : Algebra.IsStandardEtale A C := by
      convert! hf
      ext
      simp_rw [Algebra.smul_def]
      rfl
    suffices Algebra.IsStandardEtale B (TensorProduct A B C) by
      convert! this
      ext
      simp_rw [Algebra.smul_def]
      rfl
    letI : Algebra.IsStandardEtale A C := hf
    infer_instance
  have hloc ⦃A B : Type u⦄ [CommRing A] [CommRing B] (f : A →+* B)
      (hf : f.Etale) : RingHom.Locally R f := by
    letI : Algebra A B := f.toAlgebra
    letI : Algebra.Etale A B := hf
    rw [RingHom.locally_iff_span_eq_top]
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    letI : m.IsMaximal := hm
    obtain ⟨r, hr, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) m
    have hmem : R ((algebraMap B (Localization.Away r)).comp f) := by
      dsimp only [R]
      rw [← f.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_eq,
        toAlgebra_algebraMap]
      exact hstd
    exact hr (hle (Ideal.subset_span hmem))
  have hopen ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) (hf : Etale f) : IsOpenMap f := by
    letI : Etale f := hf
    exact f.isOpenMap
  have hcharts ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) (hf : Etale f) (x : X) :
      ∃ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
        (_ : x ∈ U) (e : U ≤ f ⁻¹ᵁ V), R (f.appLE V U e).hom := by
    letI : Etale f := hf
    obtain ⟨V, hV, hfx, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (f x))
    obtain ⟨U, hU, hx, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ V from hfx)
    have hlocal := hloc (f.appLE V U e).hom (f.etale_appLE hV hU e)
    rw [RingHom.locally_iff_isLocalization hRiso] at hlocal
    obtain ⟨s, hs, hfs⟩ := hlocal
    apply iSup_basicOpen_of_span_eq_top at hs
    have hx' : x ∈ (⨆ i ∈ s, X.basicOpen i) := hs.symm ▸ hx
    obtain ⟨r, hr, hrs⟩ : ∃ r ∈ s, x ∈ X.basicOpen r := by simpa using hx'
    refine ⟨V, hV, X.basicOpen r, hU.basicOpen r, hrs, (X.basicOpen_le r).trans e, ?_⟩
    rw [← f.appLE_map e (CategoryTheory.homOfLE (X.basicOpen_le r)).op]
    letI : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
    exact hfs r hr _
  have hdesc ⦃X Y : Scheme.{u}⦄ [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
      (hf : R f.appTop.hom) (hs : Surjective f) (hX : P X) : P Y :=
    (P.inverseImage AffineScheme.forgetToScheme).of_hom_of_source
      (Q := AffineScheme.standardEtale ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)
      (AffineScheme.ofHom f) ⟨hf, hs⟩ hX
  letI : (P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Etale ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme) := {
    of_hom_of_source f hf hX :=
      of_surjective_of_affine_charts P R hRiso hRbase (@Etale) hopen hcharts hdesc
        (AffineScheme.forgetToScheme.map f) hf.1 hf.2 hX }
  exact AlgebraicGeometry.Scheme.ObjectProperty.etaleLocalOfZariskiLocal P

end AlgebraicGeometry.Scheme.ObjectProperty
