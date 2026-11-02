/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import ReasLib.AlgebraicGeometry.GroupoidScheme.FlatSourceLocus
public import ReasLib.AlgebraicGeometry.GroupoidScheme.SourceLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.LocalAtSource
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Locality

/-!
# Standard source loci for groupoid schemes

This module specializes source-locus descent for groupoid schemes to standard properties of
scheme morphisms.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidScheme

private theorem fiberDimensionAt_comp_of_isOpenImmersion
    {X' X Y : Scheme.{u}} (i : X' ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] (x : X') :
    (i ≫ f).fiberDimensionAt x = f.fiberDimensionAt (i x) := by
  change topologicalKrullDimAt ((i ≫ f).asFiber x) = topologicalKrullDimAt (f.asFiber (i x))
  calc
    topologicalKrullDimAt ((i ≫ f).asFiber x) =
        topologicalKrullDimAt (⟨x, rfl⟩ : (i ≫ f) ⁻¹' {f (i x)}) :=
      topologicalKrullDimAt_eq_of_homeomorph
        ((i ≫ f).fiberHomeo ((i ≫ f) x)).symm ⟨x, rfl⟩
    _ = topologicalKrullDimAt (⟨i x, rfl⟩ : f ⁻¹' {f (i x)}) :=
      (topologicalKrullDimAt_eq_of_isOpenEmbedding
        ((f ⁻¹' {f (i x)}).restrictPreimage_isOpenEmbedding i.isOpenEmbedding)
        (⟨x, rfl⟩ : (i ≫ f) ⁻¹' {f (i x)})).symm
    _ = topologicalKrullDimAt (f.asFiber (i x)) :=
      (topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f (i x))).symm ⟨i x, rfl⟩).symm

private theorem mem_relativeDimensionLESourceLocus {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ) (x : X) :
    x ∈ MorphismProperty.sourceLocus (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d) f ↔
      f.fiberDimensionAt x ≤ (d : WithBot ℕ∞) := by
  constructor
  · intro hx
    obtain ⟨V, hxV, hV⟩ := (MorphismProperty.mem_sourceLocus
      (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d) f x).mp hx
    have hd := hV.relativeDimensionLEAt ⟨x, hxV⟩
    change (V.ι ≫ f).fiberDimensionAt ⟨x, hxV⟩ ≤ (d : WithBot ℕ∞) at hd
    simpa only [fiberDimensionAt_comp_of_isOpenImmersion, Scheme.Opens.ι_apply] using hd
  · intro hx
    let V : X.Opens := ⟨f.fiberDimensionLELocus d, f.isOpen_fiberDimensionLELocus d⟩
    have hV : Scheme.Hom.RelativeDimensionLE (V.ι ≫ f) d :=
      { toLocallyOfFiniteType := inferInstance
        relativeDimensionLEAt := fun y ↦ by
          change (V.ι ≫ f).fiberDimensionAt y ≤ (d : WithBot ℕ∞)
          rw [fiberDimensionAt_comp_of_isOpenImmersion]
          exact y.2 }
    exact MorphismProperty.sourceLocus_maximal
      (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d) f V hV hx

private theorem mem_sourceLocus_iff_affine_resLE
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P] [P.RespectsRight @IsOpenImmersion]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    x ∈ P.sourceLocus f ↔
      ∃ V : Y.affineOpens, ∃ U : X.affineOpens,
        x ∈ U.1 ∧ ∃ e : U.1 ≤ f ⁻¹ᵁ V.1, P (f.resLE V.1 U.1 e) := by
  constructor
  · intro hx
    obtain ⟨W, hxW, hW⟩ := (P.mem_sourceLocus f x).mp hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    let V : Y.Opens := V
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ W ⊓ f ⁻¹ᵁ V from ⟨hxW, hxV⟩) (W ⊓ f ⁻¹ᵁ V).isOpen
    let U : X.Opens := U
    have hUf : P (U.ι ≫ f) := by
      simpa only [← Category.assoc, Scheme.homOfLE_ι] using
        IsZariskiLocalAtSource.comp hW (X.homOfLE (hUle.trans inf_le_left))
    refine ⟨⟨V, hV⟩, ⟨U, hU⟩, hxU, hUle.trans inf_le_right, ?_⟩
    apply IsZariskiLocalAtTarget.of_isPullback
      (iX := 𝟙 U.toScheme) (f := U.ι ≫ f) (iY := V.ι) _ hUf
    exact IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  · rintro ⟨V, U, hxU, e, hf⟩
    apply (P.mem_sourceLocus f x).mpr
    refine ⟨U.1, hxU, ?_⟩
    simpa only [Scheme.Hom.resLE_comp_ι] using
      (MorphismProperty.RespectsRight.postcomp (P := P) (Q := @IsOpenImmersion)
        V.1.ι inferInstance (f.resLE V.1 U.1 e) hf)

private theorem property_resLE_iff_appLE
    (P : MorphismProperty Scheme.{u})
    (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    [HasRingHomProperty P Q] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    P (f.resLE V.1 U.1 e) ↔ Q (f.appLE V.1 U.1 e).hom := by
  letI : IsAffine V.1.toScheme := V.2
  letI : IsAffine U.1.toScheme := U.2
  exact (HasRingHomProperty.iff_of_isAffine (P := P)).trans
    ((HasRingHomProperty.isLocal_ringHomProperty P).respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V.1 U.1 e))

private theorem mem_smoothSourceLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    x ∈ MorphismProperty.sourceLocus (@Smooth) f ↔ f.SmoothAt x := by
  rw [mem_sourceLocus_iff_affine_resLE (@Smooth) f x]
  simp only [Scheme.Hom.SmoothAt, property_resLE_iff_appLE (@Smooth) (@RingHom.Smooth)]

private theorem mem_etaleSourceLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    x ∈ MorphismProperty.sourceLocus (@Etale) f ↔ f.EtaleAt x := by
  letI : MorphismProperty.RespectsRight (@Etale : MorphismProperty Scheme.{u})
      @IsOpenImmersion :=
    { postcomp := fun i hi a ha ↦ by
        letI : IsOpenImmersion i := hi
        exact MorphismProperty.comp_mem (@Etale) a i ha inferInstance }
  rw [mem_sourceLocus_iff_affine_resLE (@Etale) f x]
  simp only [Scheme.Hom.EtaleAt, property_resLE_iff_appLE (@Etale) (@RingHom.Etale)]

private theorem sourceLocus_preimage_of_isOpenImmersion
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    {X Y X' : Scheme.{u}} (f : X ⟶ Y) (i : X' ⟶ X) [IsOpenImmersion i] :
    i ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (i ≫ f) := by
  apply le_antisymm
  · apply P.sourceLocus_maximal
    simpa only [← Category.assoc, morphismRestrict_ι] using
      IsZariskiLocalAtSource.comp (P.sourceLocus_isGreatest f).1
        (i ∣_ P.sourceLocus f)
  · intro x hx
    obtain ⟨V, hxV, hV⟩ := (P.mem_sourceLocus (i ≫ f) x).mp hx
    have hImage : P ((V.ι ≫ i).opensRange.ι ≫ f) := by
      apply (P.cancel_left_of_respectsIso (V.ι ≫ i).isoOpensRange.hom _).mp
      simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι] using hV
    exact P.sourceLocus_maximal f _ hImage ⟨⟨x, hxV⟩, rfl⟩

private theorem unramifiedProperty_eq :
    (@Unramified : MorphismProperty Scheme.{u}) =
      (fun _ _ f ↦ FormallyUnramified f ∧ LocallyOfFiniteType f) := by
  funext X Y f
  exact propext ⟨fun h ↦ ⟨h.toFormallyUnramified, h.toLocallyOfFiniteType⟩,
    fun h ↦ { toFormallyUnramified := h.1, toLocallyOfFiniteType := h.2 }⟩

private theorem mem_unramifiedSourceLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    x ∈ MorphismProperty.sourceLocus (@Unramified) f ↔ f.UnramifiedAt x := by
  letI : IsZariskiLocalAtSource (@Unramified : MorphismProperty Scheme.{u}) := by
    rw [unramifiedProperty_eq]
    exact inferInstanceAs (IsZariskiLocalAtSource
      ((@FormallyUnramified ⊓ @LocallyOfFiniteType) : MorphismProperty Scheme.{u}))
  letI : IsZariskiLocalAtTarget (@Unramified : MorphismProperty Scheme.{u}) := by
    rw [unramifiedProperty_eq]
    exact inferInstanceAs (IsZariskiLocalAtTarget
      ((@FormallyUnramified ⊓ @LocallyOfFiniteType) : MorphismProperty Scheme.{u}))
  letI : MorphismProperty.RespectsRight (@Unramified : MorphismProperty Scheme.{u})
      @IsOpenImmersion :=
    { postcomp := fun i hi a ha ↦ by
        letI : IsOpenImmersion i := hi
        exact
          { toFormallyUnramified := MorphismProperty.comp_mem (@FormallyUnramified) a i
              ha.toFormallyUnramified inferInstance
            toLocallyOfFiniteType := MorphismProperty.comp_mem (@LocallyOfFiniteType) a i
              ha.toLocallyOfFiniteType inferInstance } }
  exact mem_sourceLocus_iff_affine_resLE (@Unramified) f x

private theorem locallyQuasiFiniteSourceLocus_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    CategoryTheory.MorphismProperty.sourceLocus (@LocallyQuasiFinite) f =
      f.quasiFiniteLocus := by
  apply le_antisymm
  · intro x hx
    obtain ⟨V, hxV, hV⟩ :=
      (CategoryTheory.MorphismProperty.mem_sourceLocus (@LocallyQuasiFinite) f x).mp hx
    letI : LocallyQuasiFinite (V.ι ≫ f) := hV
    exact Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp
      ((V.ι ≫ f).quasiFiniteAt ⟨x, hxV⟩)
  · exact CategoryTheory.MorphismProperty.sourceLocus_maximal
      (@LocallyQuasiFinite) f f.quasiFiniteLocus inferInstance

/-- Under locally finite-type hypotheses alone, the bounded-relative-dimension source locus
after base change descends to an open in the base-changed object scheme. -/
theorem exists_open_preimage_eq_relativeDimensionLESourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left) (d : ℕ)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    [LocallyOfFiniteType g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d)
          (pullback.snd g G.t.left ≫ G.s.left) := by
  refine exists_open_preimage_eq_sourceLocus G g
    (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d)
    (@LocallyOfFiniteType) (@LocallyOfFiniteType) le_rfl
    ?_ ?_ inferInstance inferInstance inferInstance
  · intro X Y f hf
    letI : LocallyOfFiniteType f := hf
    refine ⟨?_, fun V hV ↦ MorphismProperty.sourceLocus_maximal _ f V hV⟩
    refine { toLocallyOfFiniteType := inferInstance, relativeDimensionLEAt := ?_ }
    intro x
    change (_ ≫ f).fiberDimensionAt x ≤ (d : WithBot ℕ∞)
    rw [fiberDimensionAt_comp_of_isOpenImmersion]
    exact (mem_relativeDimensionLESourceLocus f d x.1).mp x.2
  · intro X Y X' Y' f b p f' hf _ hpb
    letI : LocallyOfFiniteType f := hf
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb hf
    ext x'
    change p x' ∈ MorphismProperty.sourceLocus
        (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d) f ↔
      x' ∈ MorphismProperty.sourceLocus (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d) f'
    rw [mem_relativeDimensionLESourceLocus, mem_relativeDimensionLESourceLocus,
      Scheme.Hom.fiberDimensionAt_eq_of_isPullback f b p f' hpb]

/-- Under locally finite-type hypotheses alone, the locally quasi-finite source locus after
base change descends to an open in the base-changed object scheme. -/
theorem exists_open_preimage_eq_locallyQuasiFiniteSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    [LocallyOfFiniteType g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@LocallyQuasiFinite : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := by
  refine exists_open_preimage_eq_sourceLocus G g (@LocallyQuasiFinite)
    (@LocallyOfFiniteType) (@LocallyOfFiniteType) le_rfl
    (fun f _ ↦ CategoryTheory.MorphismProperty.sourceLocus_isGreatest _ f)
    ?_ inferInstance inferInstance inferInstance
  intro X Y X' Y' f b p f' hf _ hpb
  letI : LocallyOfFiniteType f := hf
  letI : LocallyOfFiniteType f' :=
    CategoryTheory.MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb hf
  rw [locallyQuasiFiniteSourceLocus_eq f, locallyQuasiFiniteSourceLocus_eq f']
  ext x'
  change f.QuasiFiniteAt (p x') ↔ f'.QuasiFiniteAt x'
  have hq := (Scheme.Hom.quasiFiniteAt_iff_of_pullback_snd f b
    (hpb.isoPullback.hom x')).symm
  have hi := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := hpb.isoPullback.hom) (g := pullback.snd f b) (x := x')).symm
  simpa only [← Scheme.Hom.comp_apply, hpb.isoPullback_hom_fst,
    hpb.isoPullback_hom_snd] using hq.trans hi

/-- Under locally finite-type hypotheses alone, the unramified source locus after base change
descends to an open in the base-changed object scheme. -/
theorem exists_open_preimage_eq_unramifiedSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    [LocallyOfFiniteType g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Unramified : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := by
  letI : IsZariskiLocalAtSource (@Unramified : MorphismProperty Scheme.{u}) := by
    rw [unramifiedProperty_eq]
    exact inferInstanceAs (IsZariskiLocalAtSource
      ((@FormallyUnramified ⊓ @LocallyOfFiniteType) : MorphismProperty Scheme.{u}))
  refine exists_open_preimage_eq_sourceLocus G g (@Unramified)
    (@LocallyOfFiniteType) (@LocallyOfFiniteType) le_rfl
    (fun f _ ↦ CategoryTheory.MorphismProperty.sourceLocus_isGreatest _ f)
    ?_ inferInstance inferInstance inferInstance
  intro X Y X' Y' f b p f' hf _ hpb
  letI : LocallyOfFiniteType f := hf
  have hcan :
      pullback.fst f b ⁻¹ᵁ MorphismProperty.sourceLocus (@Unramified) f =
        MorphismProperty.sourceLocus (@Unramified) (pullback.snd f b) := by
    ext x'
    change (pullback.fst f b) x' ∈ MorphismProperty.sourceLocus (@Unramified) f ↔
      x' ∈ MorphismProperty.sourceLocus (@Unramified) (pullback.snd f b)
    rw [mem_unramifiedSourceLocus, mem_unramifiedSourceLocus]
    exact (Scheme.Hom.unramifiedAt_iff_of_pullback_snd f b x').symm
  have hiso := sourceLocus_preimage_of_isOpenImmersion (@Unramified)
    (pullback.snd f b) hpb.isoPullback.hom
  rw [← hcan] at hiso
  simpa only [← Scheme.Hom.comp_preimage, hpb.isoPullback_hom_fst,
    hpb.isoPullback_hom_snd] using hiso

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the flat source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_flatSourceLocus_of_locallyOfFinitePresentation
    {S U' : Scheme.{u}} (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Flat : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) :=
  exists_open_preimage_eq_flatSourceLocus G g

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the Cohen--Macaulay source locus descends to an open
in the base-changed object scheme. -/
theorem exists_open_preimage_eq_cohenMacaulaySourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@CohenMacaulay : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the syntomic source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_syntomicSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Syntomic : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the smooth source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_smoothSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Smooth : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := by
  refine exists_open_preimage_eq_sourceLocus G g (@Smooth) (@LocallyOfFinitePresentation)
    ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
    (fun _ _ _ h ↦ h.2)
    (fun f _ ↦ CategoryTheory.MorphismProperty.sourceLocus_isGreatest _ f)
    ?_ ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩ inferInstance
  intro X Y X' Y' f b p f' hf hb hpb
  letI : LocallyOfFinitePresentation f := hf
  letI : Flat b := hb.1
  ext x'
  change p x' ∈ MorphismProperty.sourceLocus (@Smooth) f ↔
    x' ∈ MorphismProperty.sourceLocus (@Smooth) f'
  rw [mem_smoothSourceLocus, mem_smoothSourceLocus]
  exact (Scheme.Hom.smoothAt_iff_of_isPullback_of_flat_base p f' f b hpb x').symm

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the étale source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_etaleSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Etale : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := by
  refine exists_open_preimage_eq_sourceLocus G g (@Etale) (@LocallyOfFinitePresentation)
    ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
    (fun _ _ _ h ↦ h.2)
    (fun f _ ↦ CategoryTheory.MorphismProperty.sourceLocus_isGreatest _ f)
    ?_ ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩ inferInstance
  intro X Y X' Y' f b p f' hf hb hpb
  letI : LocallyOfFinitePresentation f := hf
  letI : Flat b := hb.1
  ext x'
  change p x' ∈ MorphismProperty.sourceLocus (@Etale) f ↔
    x' ∈ MorphismProperty.sourceLocus (@Etale) f'
  rw [mem_etaleSourceLocus, mem_etaleSourceLocus]
  exact (Scheme.Hom.etaleAt_iff_of_isPullback_of_flat_base p f' f b hpb x').symm

end AlgebraicGeometry.GroupoidScheme
