module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Saturation
import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Pullback
import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Valuation

/-!
# Invariant open neighborhoods in groupoid schemes

This module constructs invariant open neighborhoods of compact open subsets under suitable
quasi-compactness, flatness, and separation hypotheses.
-/

@[expose] public section

open TopologicalSpace
open Topology
open CategoryTheory
open CategoryTheory.Over

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- If an invariant subset contains the target of an arrow, then it also contains the source. -/
private theorem source_mem_of_target_mem_of_isSetInvariant {S : Scheme.{u}}
    (G : GroupoidScheme S) {A : Set G.U.left}
    (hA : G.toPreRelation.IsSetInvariant A) {r : G.R.left} (hr : G.t.left r ∈ A) :
    G.s.left r ∈ A := by
  rw [Scheme.PreRelation.isSetInvariant_iff, G.toPreRelation_s, G.toPreRelation_t] at hA
  -- Proof comment: applying invariance to the inverse arrow swaps source and target.
  have hInvSource : G.s.left (G.i.left r) = G.t.left r := by
    simpa using congrArg (fun f ↦ f.left r) G.inverse_source
  have hInvTarget : G.t.left (G.i.left r) = G.s.left r := by
    simpa using congrArg (fun f ↦ f.left r) G.inverse_target
  have hi_source : G.s.left (G.i.left r) ∈ A := by
    rwa [hInvSource]
  have hi_target : G.t.left (G.i.left r) ∈ A := hA (G.i.left r) hi_source
  rwa [hInvTarget] at hi_target

/-- A point in the closure of the range of a quasi-compact morphism specializes from an actual
image point. -/
private theorem exists_specializingPoint_of_mem_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {y : Y} (hy : y ∈ closure (Set.range f)) :
    ∃ x : X, f x ⤳ y := by
  have hker : f.ker.support = closure (Set.range f) := Scheme.Hom.support_ker f
  have hy_support : y ∈ (f.ker.support : Set Y) := by
    rw [hker]
    exact hy
  let z : f.image := ⟨y, hy_support⟩
  obtain ⟨x, hx⟩ :=
    AlgebraicGeometry.exists_specialization_from_image_of_mem_schemeTheoreticImage f z
  -- Proof comment: mapping the specialization in the scheme-theoretic image back along `imageι`
  -- identifies the abstract image point with the original target point.
  have hmap := hx.map f.imageι.continuous
  have hz : f.imageι z = y := rfl
  have hx1 : f.imageι (f.toImage x) = f x := rfl
  refine ⟨x, ?_⟩
  exact hx1.symm ▸ hz.symm ▸ hmap

/-- The saturation `t(s⁻¹(U))` of an open subset is stable under generalization. -/
private theorem imagePreimage_stableUnderGeneralization {S : Scheme.{u}}
    (G : GroupoidScheme S) [Flat G.t.left] (U : Opens G.U.left) :
    StableUnderGeneralization (G.t.left '' (G.s.left ⁻¹' (U : Set G.U.left))) := by
  -- Proof comment: openness gives generalization stability on `U`, and flatness makes `t`
  -- a generalizing map, so the saturation inherits that stability.
  have ht_gen : GeneralizingMap G.t.left := Flat.generalizingMap G.t.left
  simpa using
    ((U.isOpen.stableUnderGeneralization).preimage G.s.left.continuous).image ht_gen

/-- Every point in the closure of `t(s⁻¹(Wᶜ))` specializes from a point already in that
bad saturation. -/
private theorem exists_specializingPoint_of_mem_closure_imagePreimageCompl {S : Scheme.{u}}
    (G : GroupoidScheme S) [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    (W : CompactOpens G.U.left) {x : G.U.left}
    (hx : x ∈ closure (G.t.left '' (G.s.left ⁻¹' ((W : Set G.U.left)ᶜ)))) :
    ∃ y ∈ G.t.left '' (G.s.left ⁻¹' ((W : Set G.U.left)ᶜ)), y ⤳ x := by
  let Z : Closeds G.U.left := ⟨(W : Set G.U.left)ᶜ, isClosed_compl_iff.mpr W.isOpen⟩
  let Zscheme : Scheme.ClosedSubschemeStructure Z :=
    Scheme.ClosedSubschemeStructure.ofIdeal (Scheme.IdealSheafData.vanishingIdeal Z)
  let Zpull : Scheme.ClosedSubschemeStructure (Z.preimage G.s.left.continuous) :=
    Scheme.ClosedSubschemeStructure.comap Zscheme G.s.left
  let tHom : G.R.left ⟶ G.U.left := G.t.left
  let f : Zpull.subscheme ⟶ G.U.left := Zpull.ι ≫ tHom
  have hRange :
      Set.range f = G.t.left '' (G.s.left ⁻¹' ((W : Set G.U.left)ᶜ)) := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨Zpull.ι r, ?_, rfl⟩
      have hmem : Zpull.ι r ∈ Set.range Zpull.ι := ⟨r, rfl⟩
      simpa [Z, Zpull] using hmem
    · rintro ⟨r, hr, rfl⟩
      have hrange : r ∈ Set.range Zpull.ι := by
        simpa [Z, Zpull] using hr
      rcases hrange with ⟨r', rfl⟩
      exact ⟨r', rfl⟩
  have hxRange : x ∈ closure (Set.range f) := by
    simpa [hRange] using hx
  obtain ⟨r, hr⟩ := exists_specializingPoint_of_mem_closure_range f hxRange
  refine ⟨f r, ?_, hr⟩
  simpa [hRange] using (show f r ∈ Set.range f from ⟨r, rfl⟩)

/-- The closure of the bad saturation `t(s⁻¹(Wᶜ))` is invariant under the groupoid action. -/
private theorem closureImagePreimageCompl_isSetInvariant {S : Scheme.{u}}
    (G : GroupoidScheme S) [QuasiCompact G.s.left] [Flat G.s.left] [QuasiCompact G.t.left]
    (W : CompactOpens G.U.left) :
    G.toPreRelation.IsSetInvariant
      (closure (G.t.left '' (G.s.left ⁻¹' ((W : Set G.U.left)ᶜ)))) := by
  let Z : Set G.U.left := (W : Set G.U.left)ᶜ
  let T : Set G.U.left := G.t.left '' (G.s.left ⁻¹' Z)
  have hT_invariant : G.toPreRelation.IsSetInvariant T := by
    simpa [T, Z] using G.isSetInvariant_image_preimage (W := Z)
  rw [Scheme.PreRelation.isSetInvariant_iff]
  rw [G.toPreRelation_s, G.toPreRelation_t]
  intro r hr
  -- Proof comment: move to a specializing point already in `T`, lift that specialization along
  -- the flat source map, and then use invariance of `T` before closing in the ambient closure.
  obtain ⟨x, hxT, hx_specializes⟩ :=
    exists_specializingPoint_of_mem_closure_imagePreimageCompl G W hr
  have hs_gen : GeneralizingMap G.s.left := Flat.generalizingMap G.s.left
  obtain ⟨r', hr'_specializes, hr'_source⟩ := hs_gen hx_specializes
  rw [Scheme.PreRelation.isSetInvariant_iff, G.toPreRelation_s, G.toPreRelation_t] at hT_invariant
  have hsT : G.s.left r' ∈ T := by
    rwa [hr'_source]
  have htT : G.t.left r' ∈ T := hT_invariant r' hsT
  have ht_specializes : G.t.left r' ⤳ G.t.left r :=
    hr'_specializes.map G.t.left.continuous
  exact ht_specializes.mem_closed isClosed_closure (subset_closure htT)

/-- When the target map is open, the canonical saturation `t(s⁻¹(W))` is represented by a
compact open subset. -/
private theorem invariantImagePreimage_isCompactOpen {S : Scheme.{u}}
    (G : GroupoidScheme S) [QuasiCompact G.s.left] (h_t : IsOpenMap G.t.left)
    (W : CompactOpens G.U.left) :
    ∃ W' : CompactOpens G.U.left,
      W'.toOpens = h_t.functor.obj (G.s.left ⁻¹ᵁ W.toOpens) := by
  let Eopen : Opens G.U.left := h_t.functor.obj (G.s.left ⁻¹ᵁ W.toOpens)
  have hCompact : IsCompact (Eopen : Set G.U.left) := by
    -- Proof comment: the open saturation is the continuous image of the compact preimage
    -- `s⁻¹(W)`, hence compact.
    have hs : IsCompact (G.s.left ⁻¹ᵁ W.toOpens : Set G.R.left) :=
      G.s.left.isCompact_preimage W.isCompact
    simpa [Eopen, IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.map_coe] using
      hs.image G.t.left.continuous
  let W' : CompactOpens G.U.left := ⟨⟨(Eopen : Set G.U.left), hCompact⟩, Eopen.isOpen⟩
  exact ⟨W', rfl⟩

/-- If both structure maps of a groupoid scheme are quasi-compact and flat and its object scheme
is quasi-separated, then every compact open is contained in an invariant open that is contained
in a compact open of the object scheme. -/
theorem exists_invariantOpen_between {S : Scheme.{u}} (G : GroupoidScheme S)
    [QuasiCompact G.s.left] [Flat G.s.left] [QuasiCompact G.t.left] [Flat G.t.left]
    [QuasiSeparatedSpace G.U.left] (W : CompactOpens G.U.left) :
    ∃ (V : Opens G.U.left) (W' : CompactOpens G.U.left),
      G.toPreRelation.IsOpenInvariant V ∧ W.toOpens ≤ V ∧ V ≤ W'.toOpens := by
  let E : Set G.U.left := G.t.left '' (G.s.left ⁻¹' (W : Set G.U.left))
  obtain ⟨𝒱, h𝒱⟩ := G.exists_compactOpenDirectedIntersection_image_preimage W
  rcases h𝒱.nonempty with ⟨W0, hW0⟩
  let Z : Set G.U.left := (W0 : Set G.U.left)ᶜ
  let T : Set G.U.left := G.t.left '' (G.s.left ⁻¹' Z)
  let V : Opens G.U.left := ⟨(closure T)ᶜ, isOpen_compl_iff.mpr isClosed_closure⟩
  have hE_invariant : G.toPreRelation.IsSetInvariant E := by
    simpa [E] using G.isSetInvariant_image_preimage (W := (W : Set G.U.left))
  have hE_subset_W0 : E ⊆ (W0 : Set G.U.left) := by
    intro x hx
    exact h𝒱.mem hx hW0
  have hW_subset_E : (W : Set G.U.left) ⊆ E := by
    intro x hx
    -- Proof comment: the identity arrow at `x` witnesses that `x` lies in its own saturation.
    refine ⟨G.e.left x, ?_, ?_⟩
    · have hs : G.s.left (G.e.left x) = x := by
        simpa using congrArg (fun f ↦ f.left x) G.identity_source
      simpa [hs] using hx
    · have ht : G.t.left (G.e.left x) = x := by
        simpa using congrArg (fun f ↦ f.left x) G.identity_target
      simpa [ht]
  have hE_gen : StableUnderGeneralization E :=
    imagePreimage_stableUnderGeneralization G W.toOpens
  have hET_disjoint : Disjoint E T := by
    refine Set.disjoint_left.mpr ?_
    intro x hxE hxT
    rcases hxT with ⟨r, hrZ, hrT⟩
    have hrtE : G.t.left r ∈ E := by
      simpa [hrT] using hxE
    have hrsE : G.s.left r ∈ E :=
      source_mem_of_target_mem_of_isSetInvariant G hE_invariant hrtE
    have hrsW0 : G.s.left r ∈ (W0 : Set G.U.left) := hE_subset_W0 hrsE
    exact hrZ hrsW0
  have hClosure_invariant :
      G.toPreRelation.IsSetInvariant (closure T) := by
    simpa [T, Z] using closureImagePreimageCompl_isSetInvariant G W0
  have hV_invariant : G.toPreRelation.IsOpenInvariant V := by
    rw [Scheme.PreRelation.isOpenInvariant_iff, Scheme.PreRelation.isSetInvariant_iff]
    rw [G.toPreRelation_s, G.toPreRelation_t]
    intro r hr
    have hs_not : G.s.left r ∉ closure T := by
      change G.s.left r ∉ closure T at hr
      exact hr
    -- Proof comment: invariance of the closed complement is the same equality of source and
    -- target preimages, read on complements.
    by_contra ht
    have ht_not : G.t.left r ∉ V := by
      exact ht
    have ht_mem : G.t.left r ∈ closure T := by
      simpa [V] using ht_not
    have hs_mem : G.s.left r ∈ closure T :=
      source_mem_of_target_mem_of_isSetInvariant G hClosure_invariant ht_mem
    exact hs_not hs_mem
  have hW_le_V : W.toOpens ≤ V := by
    intro x hx
    have hxE : x ∈ E := hW_subset_E hx
    -- Proof comment: a point of `W` lies in the good saturation `E`, so it cannot meet the
    -- closure of the bad saturation `T`.
    change x ∉ closure T
    intro hxClosure
    obtain ⟨y, hyT, hy_specializes⟩ :=
      exists_specializingPoint_of_mem_closure_imagePreimageCompl G W0 hxClosure
    have hyE : y ∈ E := hE_gen hy_specializes hxE
    exact (Set.disjoint_left.mp hET_disjoint) hyE hyT
  have hV_le_W0 : V ≤ W0.toOpens := by
    intro x hx
    by_contra hxW0
    change x ∉ (W0 : Set G.U.left) at hxW0
    have hxZ : x ∈ Z := by
      simpa [Z] using hxW0
    have hxT : x ∈ T := by
      -- Proof comment: the identity arrow at `x` keeps points of `Z` inside the bad saturation.
      refine ⟨G.e.left x, ?_, ?_⟩
      · have hs : G.s.left (G.e.left x) = x := by
          simpa using congrArg (fun f ↦ f.left x) G.identity_source
        simpa [hs] using hxZ
      · have ht : G.t.left (G.e.left x) = x := by
          simpa using congrArg (fun f ↦ f.left x) G.identity_target
        simpa [ht]
    have hxClosure : x ∈ closure T := subset_closure hxT
    have hxNotClosure : x ∉ closure T := by
      simpa [V] using hx
    exact hxNotClosure hxClosure
  exact ⟨V, W0, hV_invariant, hW_le_V, hV_le_W0⟩

/-- When the target map of a groupoid scheme is open, the saturation of a compact open is
contained in a compact open and contains the original compact open. -/
theorem exists_compactOpen_superset_of_invariantImagePreimage {S : Scheme.{u}}
    (G : GroupoidScheme S) [QuasiCompact G.s.left] (h_t : IsOpenMap G.t.left)
    (W : CompactOpens G.U.left) :
    ∃ W' : CompactOpens G.U.left,
      G.toPreRelation.IsOpenInvariant (h_t.functor.obj (G.s.left ⁻¹ᵁ W.toOpens)) ∧
        W.toOpens ≤ h_t.functor.obj (G.s.left ⁻¹ᵁ W.toOpens) ∧
        h_t.functor.obj (G.s.left ⁻¹ᵁ W.toOpens) ≤ W'.toOpens := by
  obtain ⟨W', hW'⟩ := invariantImagePreimage_isCompactOpen G h_t W
  refine ⟨W', ?_⟩
  refine ⟨G.isOpenInvariant_image_preimage h_t (W := W.toOpens), ?_, ?_⟩
  · intro x hx
    change x ∈ (W : Set G.U.left) at hx
    -- Proof comment: the identity arrow again shows that `W` is contained in its saturation.
    refine ⟨G.e.left x, ?_, ?_⟩
    · have hs : G.s.left (G.e.left x) = x := by
        simpa using congrArg (fun f ↦ f.left x) G.identity_source
      simpa [hs] using hx
    · have ht : G.t.left (G.e.left x) = x := by
        simpa using congrArg (fun f ↦ f.left x) G.identity_target
      simpa [ht, IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.map_coe]
  · simpa [hW']

end AlgebraicGeometry.GroupoidScheme
