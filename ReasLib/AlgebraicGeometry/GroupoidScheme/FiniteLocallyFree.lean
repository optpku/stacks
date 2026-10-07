module

public import Mathlib.Data.PNat.Basic
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Finite
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Saturation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations

/-!
# Finite locally free groupoid schemes

This module gives the decomposition of a groupoid scheme by the positive ranks of its
finite locally free source and target maps.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme with finite locally free source and target maps admits an exhaustive
pairwise-disjoint decomposition by invariant clopen opens on which both maps have the same
positive rank. -/
theorem exists_invariantOpenRankDecomposition {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left] :
    ∃ U : ℕ+ → Scheme.Opens G.U.left,
      iSup U = ⊤ ∧
        Pairwise (fun r q ↦ Disjoint (U r : Set G.U.left) (U q : Set G.U.left)) ∧
        ∀ r,
          IsClopen (U r : Set G.U.left) ∧
            G.toPreRelation.IsOpenInvariant (U r) ∧
            let UOver : Over S := Over.mk ((U r).ι ≫ G.U.hom)
            let inclusion : UOver ⟶ G.U := Over.homMk (U r).ι
            let restricted := G.pullback inclusion
            IsFiniteLocallyFreeOfRank restricted.s.left (r : ℕ) ∧
              IsFiniteLocallyFreeOfRank restricted.t.left (r : ℕ) := sorry

/-- Closed invariance of an ideal sheaf implies set invariance of its support. -/
private lemma supportIsSetInvariant_of_closedInvariant {S : Scheme.{u}} (G : GroupoidScheme S)
    {I : Scheme.IdealSheafData G.U.left} (hI : G.toPreRelation.IsClosedInvariant I) :
    G.toPreRelation.IsSetInvariant (I.support : Set G.U.left) := by
  -- Proof comment: invariance of the defining ideal sheaf identifies the source and target
  -- pullbacks, so the corresponding support preimages agree as sets.
  rw [Scheme.PreRelation.isSetInvariant_iff]
  rw [Scheme.PreRelation.isClosedInvariant_iff] at hI
  intro r hr
  have hr' : r ∈ (I.comap G.toPreRelation.s.left).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hr
  have ht' : r ∈ (I.comap G.toPreRelation.t.left).support := by
    simpa [hI] using hr'
  rw [Scheme.IdealSheafData.support_comap] at ht'
  exact ht'

/-- The previously constructed orbit saturations up to stage `n`. -/
private abbrev previousOrbitSaturations {S : Scheme.{u}} (G : GroupoidScheme S)
    (W : ℕ → Scheme.Opens G.U.left) (n : ℕ) : Set G.U.left :=
  ⋃ r < n, G.t.left '' (G.s.left ⁻¹' closure (W r : Set G.U.left))

/-- The recursive orbit saturations split into the previous stages and the new `n`th stage. -/
private lemma previousOrbitSaturations_succ {S : Scheme.{u}} (G : GroupoidScheme S)
    (W : ℕ → Scheme.Opens G.U.left) (n : ℕ) :
    previousOrbitSaturations G W (n + 1) =
      previousOrbitSaturations G W n ∪
        G.t.left '' (G.s.left ⁻¹' closure (W n : Set G.U.left)) := by
  ext x
  simp only [previousOrbitSaturations, Set.mem_iUnion, Set.mem_union, Set.mem_image,
    Set.mem_preimage]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact Or.inl ⟨i, hi', y, hy, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (⟨i, hi, y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨i, Nat.lt_succ_of_lt hi, y, hy, rfl⟩
    · exact ⟨n, Nat.lt_succ_self n, y, hy, rfl⟩

/-- A finite union of earlier orbit saturations is closed and invariant. -/
private lemma previousOrbitSaturations_closedInvariant {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left] (W : ℕ → Scheme.Opens G.U.left) :
    ∀ n,
      IsClosed (previousOrbitSaturations G W n) ∧
        G.toPreRelation.IsSetInvariant (previousOrbitSaturations G W n)
  | 0 => by
      -- Proof comment: there are no earlier stages at `n = 0`, so the saturation is empty.
      simp [previousOrbitSaturations, Scheme.PreRelation.isSetInvariant_iff]
  | n + 1 => by
      rcases previousOrbitSaturations_closedInvariant (G := G) (W := W) n with
        ⟨hClosedPrev, hInvariantPrev⟩
      rw [previousOrbitSaturations_succ]
      have hClosedStage :
          IsClosed (G.t.left '' (G.s.left ⁻¹' closure (W n : Set G.U.left))) := by
        -- Proof comment: the stage closure stays closed under `s`, and finiteness of `t`
        -- supplies closedness of its image.
        exact G.t.left.isClosedMap _ ((isClosed_closure).preimage G.s.left.continuous)
      have hInvariantStage :
          G.toPreRelation.IsSetInvariant
            (G.t.left '' (G.s.left ⁻¹' closure (W n : Set G.U.left))) := by
        -- Proof comment: every orbit saturation `t(s⁻¹(W))` is invariant by the general
        -- groupoid image-preimage lemma.
        simpa using AlgebraicGeometry.GroupoidScheme.isSetInvariant_image_preimage
          G (closure (W n : Set G.U.left))
      refine ⟨hClosedPrev.union hClosedStage, ?_⟩
      -- Proof comment: invariance of a union follows pointwise from invariance of each summand.
      rw [Scheme.PreRelation.isSetInvariant_iff]
      intro a ha
      rcases ha with ha | ha
      · exact Or.inl ((Scheme.PreRelation.isSetInvariant_iff _ _).mp hInvariantPrev a ha)
      · exact Or.inr ((Scheme.PreRelation.isSetInvariant_iff _ _).mp hInvariantStage a ha)

/-- If the complement of `T` is already contained in `C`, then removing `T ∪ C` leaves only
points of `T`. -/
private lemma compl_union_subset_of_compl_subset {X : Type*} {T C : Set X}
    (h : Tᶜ ⊆ C) : (T ∪ C)ᶜ ⊆ T := by
  -- Proof comment: a point outside `T ∪ C` cannot lie outside `T`, because the covering
  -- hypothesis would then force it into `C`.
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx
  by_contra hxT
  exact hx.2 (h hxT)

/-- Pulling an ideal sheaf back to an open contained in its support gives a thickening. -/
private lemma comapSubscheme_isThickening_of_subset_support {X : Scheme.{u}}
    (I : Scheme.IdealSheafData X) (W : Scheme.Opens X) (hW : (W : Set X) ⊆ I.support) :
    IsThickening (I.comap W.ι).subschemeι := by
  -- Proof comment: on an open where every point already lies in the support, the pulled-back
  -- closed subscheme has full support and hence is surjective on underlying points.
  rw [isThickening_iff]
  refine ⟨inferInstance, ?_⟩
  refine ⟨fun x ↦ ?_⟩
  change x ∈ Set.range (I.comap W.ι).subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
  exact hW x.2

/-- If an invariant subset contains the target of an arrow, then it also contains the source. -/
private lemma source_mem_of_target_mem_of_isSetInvariant {S : Scheme.{u}} (G : GroupoidScheme S)
    {A : Set G.U.left} (hA : G.toPreRelation.IsSetInvariant A) {r : G.R.left}
    (hr : G.t.left r ∈ A) : G.s.left r ∈ A := by
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

/-- The candidate ambient set for the `n`th rank stage removes the next closed stage and the
previous orbit saturations. -/
private def stageAmbientSet {S : Scheme.{u}} (G : GroupoidScheme S)
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (W : ℕ → Scheme.Opens G.U.left)
    (n : ℕ) : Set G.U.left :=
  ((((ZStage (n + 1)).support : Set G.U.left) ∪ previousOrbitSaturations G W n)ᶜ)

/-- The candidate ambient stage is open because it is the complement of two closed pieces. -/
private lemma stageAmbientSet_isOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (W : ℕ → Scheme.Opens G.U.left) (n : ℕ) :
    IsOpen (stageAmbientSet G ZStage W n) := by
  rcases previousOrbitSaturations_closedInvariant (G := G) (W := W) n with ⟨hClosedPrev, _⟩
  have hClosedNext : IsClosed ((ZStage (n + 1)).support : Set G.U.left) := by
    simpa [Scheme.IdealSheafData.range_subschemeι] using
      (IsClosedImmersion.isClosedEmbedding (f := (ZStage (n + 1)).subschemeι)).isClosed_range
  -- Proof comment: complements of closed unions are open.
  simpa [stageAmbientSet] using (hClosedNext.union hClosedPrev).isOpen_compl

/-- The candidate ambient stage packaged as an open subscheme of `G.U.left`. -/
private noncomputable def stageAmbientOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (W : ℕ → Scheme.Opens G.U.left)
    (n : ℕ) : Scheme.Opens G.U.left :=
  ⟨stageAmbientSet G ZStage W n, stageAmbientSet_isOpen G ZStage W n⟩

/-- Once the previously covered orbit saturations contain the complement of the current closed
stage, the ambient candidate lies inside that current stage. -/
private lemma stageAmbientOpen_subset_support {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (W : ℕ → Scheme.Opens G.U.left) (n : ℕ)
    (hCover : ((ZStage n).support : Set G.U.left)ᶜ ⊆ previousOrbitSaturations G W n) :
    (stageAmbientOpen G ZStage W n : Set G.U.left) ⊆ (ZStage n).support := by
  intro x hx
  change x ∈ stageAmbientSet G ZStage W n at hx
  have hxNotUnion :
      x ∉ ((ZStage (n + 1)).support : Set G.U.left) ∪ previousOrbitSaturations G W n := by
    simpa [stageAmbientSet] using hx
  have hxNotPrev : x ∉ previousOrbitSaturations G W n := by
    exact fun hxPrev ↦ hxNotUnion (Or.inr hxPrev)
  -- Proof comment: points outside the current support were already covered earlier, so a new
  -- stage point cannot lie outside the current support.
  by_contra hxSupport
  exact hxNotPrev (hCover hxSupport)

/-- The candidate ambient stage avoids the next closed stage by construction. -/
private lemma stageAmbientOpen_disjoint_nextSupport {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (W : ℕ → Scheme.Opens G.U.left) (n : ℕ) :
    Disjoint (stageAmbientOpen G ZStage W n : Set G.U.left)
      ((ZStage (n + 1)).support : Set G.U.left) := by
  refine Set.disjoint_left.mpr ?_
  intro x hxStage hxNext
  change x ∈ stageAmbientSet G ZStage W n at hxStage
  have hxNotUnion :
      x ∉ ((ZStage (n + 1)).support : Set G.U.left) ∪ previousOrbitSaturations G W n := by
    simpa [stageAmbientSet] using hxStage
  have hxNotNext : x ∉ (ZStage (n + 1)).support := by
    exact fun hxNext' ↦ hxNotUnion (Or.inl hxNext')
  exact hxNotNext hxNext

/-- Closed invariance of the next stage and invariance of the previous orbit saturations make the
ambient candidate itself invariant. -/
private lemma stageAmbientOpen_invariant {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left)
    (hZ_invariant : ∀ r, G.toPreRelation.IsClosedInvariant (ZStage r))
    (W : ℕ → Scheme.Opens G.U.left) (n : ℕ) :
    G.toPreRelation.IsOpenInvariant (stageAmbientOpen G ZStage W n) := by
  rcases previousOrbitSaturations_closedInvariant (G := G) (W := W) n with
    ⟨_, hPrevInvariant⟩
  let nextSupport : Set G.U.left := (ZStage (n + 1)).support
  have hNextInvariant : G.toPreRelation.IsSetInvariant nextSupport :=
    supportIsSetInvariant_of_closedInvariant G (hZ_invariant (n + 1))
  have hUnionInvariant :
      G.toPreRelation.IsSetInvariant (nextSupport ∪ previousOrbitSaturations G W n) := by
    rw [Scheme.PreRelation.isSetInvariant_iff]
    intro r hr
    rcases hr with hr | hr
    · exact Or.inl ((Scheme.PreRelation.isSetInvariant_iff _ _).mp hNextInvariant r hr)
    · exact Or.inr ((Scheme.PreRelation.isSetInvariant_iff _ _).mp hPrevInvariant r hr)
  rw [Scheme.PreRelation.isOpenInvariant_iff, Scheme.PreRelation.isSetInvariant_iff]
  rw [G.toPreRelation_s, G.toPreRelation_t]
  intro r hr
  change G.s.left r ∈ stageAmbientSet G ZStage W n at hr
  have hsNotUnion : G.s.left r ∉ nextSupport ∪ previousOrbitSaturations G W n := by
    exact hr
  -- Proof comment: the complement of an invariant union is invariant because the inverse arrow
  -- turns target-membership in the union back into source-membership.
  by_contra ht
  change G.t.left r ∉ stageAmbientSet G ZStage W n at ht
  have htUnion : G.t.left r ∈ nextSupport ∪ previousOrbitSaturations G W n := by
    by_contra htNotUnion
    apply ht
    change G.t.left r ∉ nextSupport ∪ previousOrbitSaturations G W n
    exact htNotUnion
  exact hsNotUnion (source_mem_of_target_mem_of_isSetInvariant G hUnionInvariant htUnion)

/-- The previous orbit saturations up to stage `n` only depend on the earlier stages. -/
private lemma previousOrbitSaturations_congr {S : Scheme.{u}} (G : GroupoidScheme S)
    {W W' : ℕ → Scheme.Opens G.U.left} {n : ℕ}
    (hWW' : ∀ r < n, W r = W' r) :
    previousOrbitSaturations G W n = previousOrbitSaturations G W' n := by
  -- Proof comment: the defining union only ranges over indices `r < n`, so equality on those
  -- earlier stages identifies the whole saturation set.
  ext x
  simp only [previousOrbitSaturations, Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    refine ⟨r, hr, y, ?_, rfl⟩
    simpa [hWW' r hr] using hy
  · rintro ⟨r, hr, y, hy, rfl⟩
    refine ⟨r, hr, y, ?_, rfl⟩
    simpa [hWW' r hr] using hy

/-- The ambient stage at index `n` only depends on the stages with smaller index. -/
private lemma stageAmbientOpen_congr {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left)
    {W W' : ℕ → Scheme.Opens G.U.left} (n : ℕ)
    (hWW' : ∀ r < n, W r = W' r) :
    stageAmbientOpen G ZStage W n = stageAmbientOpen G ZStage W' n := by
  -- Proof comment: after replacing the earlier orbit saturations by the congruent family, the
  -- two open subsets have the same defining set.
  ext x
  simp only [stageAmbientOpen, stageAmbientSet, previousOrbitSaturations_congr G hWW']

/-- The recursively defined ambient stage family from the rank stratification. -/
private noncomputable def stageAmbientFamily {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) : ℕ → Scheme.Opens G.U.left
  | n =>
      stageAmbientOpen G ZStage
        (fun r ↦ if _h : r < n then stageAmbientFamily G ZStage r else ⊥) n
termination_by n => n
decreasing_by
  exact _h

/-- The recursive stage family satisfies the defining stage equation at every index. -/
private lemma stageAmbientFamily_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (n : ℕ) :
    stageAmbientFamily G ZStage n =
      stageAmbientOpen G ZStage (stageAmbientFamily G ZStage) n := by
  -- Proof comment: the recursion fills the irrelevant later indices with `⊥`, and the previous
  -- congruence lemma removes that padding because stage `n` only uses stages `< n`.
  have hdef :
      stageAmbientFamily G ZStage n =
        stageAmbientOpen G ZStage
          (fun r ↦ if h : r < n then stageAmbientFamily G ZStage r else ⊥) n := by
    simpa using stageAmbientFamily.eq_1 (G := G) (ZStage := ZStage) n
  calc
    stageAmbientFamily G ZStage n =
        stageAmbientOpen G ZStage
          (fun r ↦ if h : r < n then stageAmbientFamily G ZStage r else ⊥) n := hdef
    _ = stageAmbientOpen G ZStage (stageAmbientFamily G ZStage) n := by
      exact stageAmbientOpen_congr G ZStage n (fun r hr ↦ by exact if_pos hr)

/-- The recursive ambient stages cover the complement of each rank support by the previous orbit
saturations. -/
private lemma stageComplement_subset_previousOrbitSaturations {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (hZ0 : ZStage 0 = ⊥) :
    ∀ n,
      ((ZStage n).support : Set G.U.left)ᶜ ⊆
        previousOrbitSaturations G (stageAmbientFamily G ZStage) n
  | 0 => by
      -- Proof comment: the zeroth stage is the whole scheme, so there is no uncovered point.
      simp [hZ0, previousOrbitSaturations]
  | n + 1 => by
      intro x hxNext
      rw [previousOrbitSaturations_succ]
      by_cases hxPrev :
          x ∈ previousOrbitSaturations G (stageAmbientFamily G ZStage) n
      · exact Or.inl hxPrev
      · have hxCurr : x ∈ (ZStage n).support := by
          by_contra hxCurr
          exact hxPrev
            (stageComplement_subset_previousOrbitSaturations G ZStage hZ0 n hxCurr)
        have hxStage : x ∈ (stageAmbientFamily G ZStage n : Set G.U.left) := by
          rw [stageAmbientFamily_eq G ZStage n]
          change x ∈ stageAmbientSet G ZStage (stageAmbientFamily G ZStage) n
          have hxNotUnion :
              x ∉ ((ZStage (n + 1)).support : Set G.U.left) ∪
                previousOrbitSaturations G (stageAmbientFamily G ZStage) n := by
            exact fun hxUnion ↦ hxUnion.elim hxNext hxPrev
          simpa [stageAmbientSet] using hxNotUnion
        have hs : G.s.left (G.e.left x) = x := by
          simpa using congrArg (fun f ↦ f.left x) G.identity_source
        have ht : G.t.left (G.e.left x) = x := by
          simpa using congrArg (fun f ↦ f.left x) G.identity_target
        refine Or.inr ?_
        refine ⟨G.e.left x, ?_, ht⟩
        simpa [hs] using subset_closure hxStage

/-- Each recursive ambient stage lies inside the corresponding rank support. -/
private lemma stageAmbientFamily_subset_support {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (hZ0 : ZStage 0 = ⊥) (n : ℕ) :
    (stageAmbientFamily G ZStage n : Set G.U.left) ⊆ (ZStage n).support := by
  -- Proof comment: the recursive cover invariant is exactly the input required by the generic
  -- subset-support lemma for each ambient stage.
  rw [stageAmbientFamily_eq G ZStage n]
  exact stageAmbientOpen_subset_support G ZStage (stageAmbientFamily G ZStage) n
    (stageComplement_subset_previousOrbitSaturations G ZStage hZ0 n)

/-- Each recursive ambient stage is invariant under the groupoid action. -/
private lemma stageAmbientFamily_invariant {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left)
    (hZ_invariant : ∀ r, G.toPreRelation.IsClosedInvariant (ZStage r)) (n : ℕ) :
    G.toPreRelation.IsOpenInvariant (stageAmbientFamily G ZStage n) := by
  -- Proof comment: after unfolding the recursive stage equation, invariance is the generic
  -- invariance statement for the ambient stage operator.
  rw [stageAmbientFamily_eq G ZStage n]
  exact stageAmbientOpen_invariant G ZStage hZ_invariant (stageAmbientFamily G ZStage) n

/-- A point of an earlier recursive ambient stage already lies in every later orbit
saturation union. -/
private lemma mem_previousOrbitSaturations_of_mem_stageAmbientFamily {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) {m n : ℕ} (hmn : m < n)
    {x : G.U.left} (hx : x ∈ stageAmbientFamily G ZStage m) :
    x ∈ previousOrbitSaturations G (stageAmbientFamily G ZStage) n := by
  -- Proof comment: the identity arrow places `x` in the orbit saturation generated by the
  -- closure of its own stage, and this summand appears in every later saturation union.
  have hs : G.s.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_source
  have ht : G.t.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_target
  change x ∈ ⋃ r < n,
      G.t.left '' (G.s.left ⁻¹' closure (stageAmbientFamily G ZStage r : Set G.U.left))
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
  refine ⟨m, hmn, G.e.left x, ?_, ht⟩
  simpa [hs] using subset_closure hx

/-- Points of the `n`th recursive ambient stage avoid the earlier orbit saturations by
construction. -/
private lemma stageAmbientFamily_not_mem_previousOrbitSaturations {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) {n : ℕ} {x : G.U.left}
    (hx : x ∈ stageAmbientFamily G ZStage n) :
    x ∉ previousOrbitSaturations G (stageAmbientFamily G ZStage) n := by
  -- Proof comment: the recursive stage is defined by removing the previous orbit saturations.
  rw [stageAmbientFamily_eq G ZStage n] at hx
  change x ∈ stageAmbientSet G ZStage (stageAmbientFamily G ZStage) n at hx
  have hxNotUnion :
      x ∉ ((ZStage (n + 1)).support : Set G.U.left) ∪
        previousOrbitSaturations G (stageAmbientFamily G ZStage) n := by
    simpa [stageAmbientSet] using hx
  exact fun hxPrev ↦ hxNotUnion (Or.inr hxPrev)

/-- Each recursive ambient stage misses the next rank support. -/
private lemma stageAmbientFamily_disjoint_nextSupport {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) (n : ℕ) :
    Disjoint (stageAmbientFamily G ZStage n : Set G.U.left)
      ((ZStage (n + 1)).support : Set G.U.left) := by
  -- Proof comment: after rewriting the recursive stage equation, this is exactly the generic
  -- ambient-stage disjointness lemma.
  rw [stageAmbientFamily_eq G ZStage n]
  exact stageAmbientOpen_disjoint_nextSupport G ZStage (stageAmbientFamily G ZStage) n

/-- Distinct recursive ambient stages are pairwise disjoint. -/
private lemma stageAmbientFamily_pairwiseDisjoint {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left]
    (ZStage : ℕ →o Scheme.IdealSheafData G.U.left) :
    Pairwise (fun m n ↦
      Disjoint (stageAmbientFamily G ZStage m : Set G.U.left)
        (stageAmbientFamily G ZStage n : Set G.U.left)) := by
  intro m n hmn
  rcases Nat.lt_or_gt_of_ne hmn with hmn' | hnm'
  · refine Set.disjoint_left.mpr ?_
    intro x hxM hxN
    have hxPrev :
        x ∈ previousOrbitSaturations G (stageAmbientFamily G ZStage) n :=
      mem_previousOrbitSaturations_of_mem_stageAmbientFamily G ZStage hmn' hxM
    exact (stageAmbientFamily_not_mem_previousOrbitSaturations G ZStage hxN) hxPrev
  · refine Set.disjoint_left.mpr ?_
    intro x hxM hxN
    have hxPrev :
        x ∈ previousOrbitSaturations G (stageAmbientFamily G ZStage) m :=
      mem_previousOrbitSaturations_of_mem_stageAmbientFamily G ZStage hnm' hxN
    exact (stageAmbientFamily_not_mem_previousOrbitSaturations G ZStage hxM) hxPrev

/-- A groupoid scheme with finite source and target maps admits an invariant open subscheme
and an invariant closed thickening whose closure meets every orbit and whose restricted source
and target maps are finite locally free. -/
theorem exists_invariantOpenThickening {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left] :
    ∃ (W : Scheme.Opens G.U.left) (Z : Scheme.IdealSheafData (W : Scheme)),
      let i : Over.mk ((Z.subschemeι ≫ W.ι) ≫ G.U.hom) ⟶ G.U :=
        Over.homMk (Z.subschemeι ≫ W.ι)
      G.toPreRelation.IsOpenInvariant W ∧
        G.toPreRelation.IsInvariant (Subobject.mk (Z.subschemeι ≫ W.ι)) ∧
          G.t.left '' (G.s.left ⁻¹' closure (W : Set G.U.left)) = Set.univ ∧
            IsThickening Z.subschemeι ∧
              IsFiniteLocallyFree (G.pullback i).s.left ∧
                IsFiniteLocallyFree (G.pullback i).t.left := by
  rcases exists_invariantRankStratification G with ⟨ZStage, hZ0, hZ_invariant, hZ_inter, hRank⟩
  have hStageSupport :
      ∀ {n} {C : Set G.U.left},
        (((ZStage n).support : Set G.U.left)ᶜ ⊆ C) →
          ((((ZStage n).support : Set G.U.left) ∪ C)ᶜ) ⊆ (ZStage n).support := by
    intro n C hC
    exact compl_union_subset_of_compl_subset hC
  have hStageThickening :
      ∀ {n} (Wn : Scheme.Opens G.U.left),
        (Wn : Set G.U.left) ⊆ (ZStage n).support →
          IsThickening ((ZStage n).comap Wn.ι).subschemeι := by
    intro n Wn hWn
    exact comapSubscheme_isThickening_of_subset_support (I := ZStage n) Wn hWn
  have hStageAmbientSupport :
      ∀ (W : ℕ → Scheme.Opens G.U.left) (n : ℕ),
        ((ZStage n).support : Set G.U.left)ᶜ ⊆ previousOrbitSaturations G W n →
          (stageAmbientOpen G ZStage W n : Set G.U.left) ⊆ (ZStage n).support := by
    intro W n hCover
    exact stageAmbientOpen_subset_support G ZStage W n hCover
  have hStageAmbientInvariant :
      ∀ (W : ℕ → Scheme.Opens G.U.left) (n : ℕ),
        G.toPreRelation.IsOpenInvariant (stageAmbientOpen G ZStage W n) := by
    intro W n
    exact stageAmbientOpen_invariant G ZStage hZ_invariant W n
  let WStage : ℕ → Scheme.Opens G.U.left := stageAmbientFamily G ZStage
  have hWStage_eq :
      ∀ n, WStage n = stageAmbientOpen G ZStage WStage n := by
    -- Proof comment: the recursive family already satisfies the defining stage equation.
    intro n
    simpa [WStage] using stageAmbientFamily_eq G ZStage n
  have hWStage_cover :
      ∀ n,
        ((ZStage n).support : Set G.U.left)ᶜ ⊆ previousOrbitSaturations G WStage n := by
    -- Proof comment: the inductive cover invariant is now a proved lemma on the recursive family.
    intro n
    simpa [WStage] using stageComplement_subset_previousOrbitSaturations G ZStage hZ0 n
  have hWStage_subset :
      ∀ n, (WStage n : Set G.U.left) ⊆ (ZStage n).support := by
    -- Proof comment: each stage sits inside the current rank support because uncovered points
    -- were already absorbed by earlier orbit saturations.
    intro n
    simpa [WStage] using stageAmbientFamily_subset_support G ZStage hZ0 n
  have hWStage_invariant :
      ∀ n, G.toPreRelation.IsOpenInvariant (WStage n) := by
    -- Proof comment: each recursive stage inherits invariance from the ambient-stage operator.
    intro n
    simpa [WStage] using stageAmbientFamily_invariant G ZStage hZ_invariant n
  have hWStage_disjoint_next :
      ∀ n, Disjoint (WStage n : Set G.U.left) ((ZStage (n + 1)).support : Set G.U.left) := by
    -- Proof comment: every stage was constructed by removing the next rank support.
    intro n
    simpa [WStage] using stageAmbientFamily_disjoint_nextSupport G ZStage n
  have hWStage_pairwise :
      Pairwise (fun m n ↦ Disjoint (WStage m : Set G.U.left) (WStage n : Set G.U.left)) := by
    -- Proof comment: later stages exclude the earlier orbit saturations, and the identity arrow
    -- puts every earlier-stage point into its own saturation.
    simpa [WStage] using stageAmbientFamily_pairwiseDisjoint G ZStage
  have hWStageThickening :
      ∀ n, IsThickening ((ZStage n).comap (WStage n).ι).subschemeι := by
    -- Proof comment: once a stage is known to lie inside the corresponding support, its comap
    -- closed immersion is automatically a thickening.
    intro n
    exact hStageThickening (WStage n) (hWStage_subset n)
  -- It remains to compare each stage thickening with its canonical rank-open complement,
  -- transport the corresponding rank statement, and assemble the stage coproduct over
  -- `W := iSup WStage`.
  sorry

end AlgebraicGeometry.GroupoidScheme
