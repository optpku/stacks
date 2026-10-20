/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.AlgebraicGeometry.GroupoidScheme.PreRelation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Point
public import ReasLib.Topology.CompactOpen.Neighborhood

/-!
# Saturations in groupoid schemes

This module gives compact-open intersection presentations of the saturation of a compact open
subset under a groupoid scheme.
-/

@[expose] public section

open TopologicalSpace
open TopologicalSpace.Compacts.CompactOpenNhds

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The target image of the source preimage of a subset is invariant under a groupoid scheme. -/
theorem isSetInvariant_image_preimage {S : Scheme.{u}} (G : GroupoidScheme S)
    (W : Set G.U.left) :
    G.toPreRelation.IsSetInvariant (G.t.left '' (G.s.left ⁻¹' W)) := by
  -- Reinterpret invariance as stability of the saturation under moving along one more arrow.
  rw [Scheme.PreRelation.isSetInvariant_iff_preimage_subset]
  intro r hr
  rw [Set.mem_preimage] at hr ⊢
  rw [G.toPreRelation_s] at hr
  rw [G.toPreRelation_t]
  rw [Set.mem_image] at hr ⊢
  -- Lemmas 39.3.4 and 39.13.2 identify the induced point relation with an equivalence.
  have hEquiv := Scheme.PreRelation.pointRelIsEquivalence G.toPreRelation
    (G.toPreRelation_isPreEquivalence)
  simp_rw [G.toPreRelation_t, G.toPreRelation_s] at hEquiv
  rcases hr with ⟨q, hqW, hq_t⟩
  -- Compose the arrow witnessing `t q ∈ s⁻¹(W)` with `r`.
  have hRelated :
      ∃ u : G.R.left, G.t.left u = G.t.left r ∧ G.s.left u = G.s.left q := by
    exact hEquiv.trans ⟨r, rfl, rfl⟩ ⟨q, hq_t, rfl⟩
  rcases hRelated with ⟨u, hu_t, hu_s⟩
  refine ⟨u, ?_, hu_t⟩
  simpa [Set.mem_preimage, hu_s] using hqW

/-- If the target map of a groupoid scheme is open, the saturation of an open subset is an
invariant open. -/
theorem isOpenInvariant_image_preimage {S : Scheme.{u}} (G : GroupoidScheme S)
    (h_t : IsOpenMap (G.t.left).base) (W : Opens G.U.left) :
    G.toPreRelation.IsOpenInvariant (h_t.functor.obj (G.s.left ⁻¹ᵁ W)) := by
  -- Open invariance is set invariance for the underlying open subset.
  rw [Scheme.PreRelation.isOpenInvariant_iff]
  simpa [IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.map_coe] using
    G.isSetInvariant_image_preimage (W := (W : Set G.U.left))

/-- If the target map of a groupoid scheme is open and both structure maps are quasi-compact,
the object scheme admits a cover by invariant compact open subsets. -/
theorem exists_invariantCompactOpenCover {S : Scheme.{u}} (G : GroupoidScheme S)
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    (h_t : IsOpenMap (G.t.left).base) :
    ∃ (ι : Type u) (𝒰 : ι → CompactOpens G.U.left),
      IsOpenCover (fun i ↦ (𝒰 i).toOpens) ∧
        ∀ i, G.toPreRelation.IsOpenInvariant (𝒰 i).toOpens := by
  -- Each saturated affine open is compact because quasi-compact preimages of compact opens
  -- remain compact and continuous images preserve compactness.
  have hCompact :
      ∀ V : G.U.left.affineOpens,
        IsCompact (((h_t.functor.obj (G.s.left ⁻¹ᵁ (V : G.U.left.Opens))) :
          G.U.left.Opens) : Set G.U.left) := by
    intro V
    simpa [IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.map_coe] using
      (G.s.left.isCompact_preimage V.2.isCompact).image G.t.left.continuous
  -- Every affine open sits inside its saturation by using the identity arrow at each point.
  have hSubset :
      ∀ V : G.U.left.affineOpens,
        ((V : G.U.left.Opens) : Set G.U.left) ⊆
          (((h_t.functor.obj (G.s.left ⁻¹ᵁ (V : G.U.left.Opens))) :
            G.U.left.Opens) : Set G.U.left) := by
    intro V x hx
    have hs : G.s.left (G.e.left x) = x := by
      simpa using congrArg (fun f ↦ f.left x) G.identity_source
    have ht : G.t.left (G.e.left x) = x := by
      simpa using congrArg (fun f ↦ f.left x) G.identity_target
    refine ⟨G.e.left x, ?_, ht⟩
    simpa [TopologicalSpace.Opens.map_coe, hs] using hx
  let 𝒰 : G.U.left.affineOpens → CompactOpens G.U.left := fun V ↦
    let W : G.U.left.Opens := h_t.functor.obj (G.s.left ⁻¹ᵁ (V : G.U.left.Opens))
    ⟨⟨(W : Set G.U.left), hCompact V⟩, W.isOpen⟩
  have h𝒰_toOpens :
      ∀ V : G.U.left.affineOpens,
        (𝒰 V).toOpens = h_t.functor.obj (G.s.left ⁻¹ᵁ (V : G.U.left.Opens)) := by
    intro V
    rfl
  have hAffineCover : IsOpenCover (fun V : G.U.left.affineOpens ↦ (V : G.U.left.Opens)) :=
    iSup_affineOpens_eq_top G.U.left
  have hCover : IsOpenCover (fun V ↦ (𝒰 V).toOpens) := by
    -- The affine-open cover enlarges to the saturated cover because each affine open is contained
    -- in its own saturation.
    apply TopologicalSpace.IsOpenCover.mk
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨V, hxV⟩ := hAffineCover.exists_mem x
      exact (le_iSup (fun V => (𝒰 V).toOpens) V) (hSubset V hxV)
  refine ⟨G.U.left.affineOpens, 𝒰, hCover, ?_⟩
  intro V
  -- Each compact open in the cover is the invariant saturation from part (2).
  rw [h𝒰_toOpens V]
  exact G.isOpenInvariant_image_preimage h_t (W := (V : G.U.left.Opens))

/-- The target image of the source preimage of a compact open subset of the object scheme is a
directed intersection of compact open subsets. -/
theorem exists_compactOpenDirectedIntersection_image_preimage {S : Scheme.{u}}
    (G : GroupoidScheme S) [QuasiCompact G.s.left] [Flat G.t.left]
    [QuasiSeparatedSpace G.U.left] (W : CompactOpens G.U.left) :
    ∃ 𝒱 : Set (CompactOpens G.U.left),
      IsCompactOpenDirectedIntersection
        (G.t.left '' (G.s.left ⁻¹' (W : Set G.U.left))) 𝒱 := by
  let s := G.s.left
  let t := G.t.left
  let E : Set G.U.left := t '' (s ⁻¹' (W : Set G.U.left))
  have hE_compact : IsCompact E := by
    have hs : IsCompact (s ⁻¹ᵁ W.toOpens : Set G.R.left) :=
      s.isCompact_preimage W.isCompact
    simpa [E] using hs.image t.continuous
  have hE_gen : StableUnderGeneralization E := by
    have ht_gen : GeneralizingMap t := Flat.generalizingMap t
    simpa [E] using
      (W.isOpen.stableUnderGeneralization).preimage s.continuous |>.image ht_gen
  have hnhds : nhdsKer E = E := by
    refine Set.Subset.antisymm ?_ subset_nhdsKer
    intro x hx
    rcases mem_nhdsKer_iff_specializes.mp hx with ⟨y, hy, hxy⟩
    exact hE_gen hxy hy
  let K : Compacts G.U.left := ⟨E, hE_compact⟩
  refine ⟨TopologicalSpace.Compacts.compactOpenNhds K, ?_⟩
  simpa [E, K, hnhds] using isDirectedIntersection K

/-- If both structure maps of a groupoid scheme are quasi-compact and flat and its object scheme
is quasi-separated, the saturation of a compact open is the intersection of a nonempty family of
compact open subsets. -/
theorem exists_compactOpens_image_preimage {S : Scheme.{u}} (G : GroupoidScheme S)
    [QuasiCompact G.s.left] [Flat G.s.left] [QuasiCompact G.t.left] [Flat G.t.left]
    [QuasiSeparatedSpace G.U.left] (W : CompactOpens G.U.left) :
    ∃ 𝒱 : Set (CompactOpens G.U.left), 𝒱.Nonempty ∧
      G.t.left '' (G.s.left ⁻¹' (W : Set G.U.left)) =
        ⋂ V ∈ 𝒱, (V : Set G.U.left) := by
  obtain ⟨𝒱, h𝒱⟩ := G.exists_compactOpenDirectedIntersection_image_preimage W
  exact ⟨𝒱, h𝒱.nonempty, h𝒱.eq_iInter⟩

end AlgebraicGeometry.GroupoidScheme
