/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Prod
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.Group.GroupTopology
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Instances.Rat

/-!
# A sequential system of abelian topological groups with distinct colimit topologies

The stages are `ℚ × ℝ^{n+1}` with the Euclidean product topology, and the
successor maps pad a trailing zero on the real coordinates. The algebraic sequential
colimit is `ℚ × (ℕ →₀ ℝ)`. Its colimit topology in `TopCat` is the final topology of
the stage inclusions; its colimit topology in topological groups is the finest additive
group topology making those inclusions continuous.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Topology

namespace TopCat.Counterexample.NatAddGroupColimit

/-- The `n`-th stage is the product of the rationals and `n + 1` real coordinates. -/
abbrev stage (n : ℕ) : Type :=
  ℚ × (Fin (n + 1) → ℝ)

/-- The rational-real product stage bundled with its Euclidean product topology. -/
def stageSpace (n : ℕ) : TopCat.{0} :=
  TopCat.of (stage n)

/-- The algebraic sequential colimit of the stages. -/
abbrev colimitCarrier : Type :=
  ℚ × (ℕ →₀ ℝ)

noncomputable section

/-- The additive successor `(q, v) ↦ (q, Fin.snoc v 0)`, via zero-padding along
`Fin.castSuccEmb`. -/
def stageTransitionHom (n : ℕ) : stage n →+ stage (n + 1) :=
  (AddMonoidHom.id ℚ).prodMap <|
    (Finsupp.addEquivFunOnFinite :
        (Fin (n + 2) →₀ ℝ) ≃+ (Fin (n + 2) → ℝ)).toAddMonoidHom.comp
      ((Finsupp.embDomain.addMonoidHom (Fin.castSuccEmb : Fin (n + 1) ↪ Fin (n + 2))).comp
        (Finsupp.addEquivFunOnFinite :
            (Fin (n + 1) →₀ ℝ) ≃+ (Fin (n + 1) → ℝ)).symm.toAddMonoidHom)

/-- The additive successor pads a trailing zero on the real coordinates. -/
theorem stageTransitionHom_apply (n : ℕ) (q : ℚ) (v : Fin (n + 1) → ℝ) :
    stageTransitionHom n (q, v) = (q, Fin.snoc v 0) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      change Finsupp.embDomain Fin.castSuccEmb (Finsupp.equivFunOnFinite.symm v)
        (Fin.last (n + 1)) = 0
      apply Finsupp.embDomain_notin_range
      rintro ⟨j, hj⟩
      have h := congrArg Fin.val hj
      exact (Nat.ne_of_lt j.isLt) h
    · simp only [Fin.snoc_castSucc]
      change Finsupp.embDomain Fin.castSuccEmb (Finsupp.equivFunOnFinite.symm v)
        (Fin.castSuccEmb j) = v j
      exact Finsupp.embDomain_apply_self Fin.castSuccEmb _ j

/-- The Euclidean successor maps are continuous. -/
theorem stageTransition_continuous (n : ℕ) :
    Continuous (stageTransitionHom n : stage n → stage (n + 1)) := by
  have h : (stageTransitionHom n : stage n → stage (n + 1)) =
      fun x => (x.1, Fin.snoc x.2 0) := by
    funext x
    exact stageTransitionHom_apply n x.1 x.2
  rw [h]
  apply Continuous.prodMk continuous_fst
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using
      (continuous_const : Continuous (fun _ : stage n => (0 : ℝ)))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (continuous_apply j).comp continuous_snd

/-- The continuous successor morphism between adjacent bundled stage spaces. -/
def stageTransition (n : ℕ) : stageSpace n ⟶ stageSpace (n + 1) :=
  TopCat.ofHom ⟨stageTransitionHom n, stageTransition_continuous n⟩

/-- The successor maps are closed embeddings. -/
theorem isClosedEmbedding_stageTransition (n : ℕ) :
    Topology.IsClosedEmbedding (stageTransitionHom n : stage n → stage (n + 1)) := by
  let r : stage (n + 1) → stage n := fun x => (x.1, fun i => x.2 i.castSucc)
  have hr : Function.LeftInverse r (stageTransitionHom n) := by
    rintro ⟨q, v⟩
    simp [r, stageTransitionHom_apply]
  exact hr.isClosedEmbedding (by fun_prop) (stageTransition_continuous n)

/-- The rational-real product stages and zero-padding maps form a sequential diagram. -/
def system : ℕ ⥤ TopCat.{0} :=
  Functor.ofSequence stageTransition

/-- The objects of `system` are the bundled stage spaces. -/
theorem system_obj (n : ℕ) : system.obj n = stageSpace n :=
  rfl

/-- The algebraic inclusion of stage `n` into the finite-support colimit carrier. -/
def stageι (n : ℕ) : stage n →+ colimitCarrier :=
  (AddMonoidHom.id ℚ).prodMap <|
    (Finsupp.embDomain.addMonoidHom Fin.valEmbedding).comp
      (Finsupp.addEquivFunOnFinite :
          (Fin (n + 1) →₀ ℝ) ≃+ (Fin (n + 1) → ℝ)).symm.toAddMonoidHom

/-- The stage inclusion extends the real coordinates by zero to a finitely supported function. -/
theorem stageι_apply (n : ℕ) (q : ℚ) (v : Fin (n + 1) → ℝ) :
    stageι n (q, v) =
      (q, Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm v)) :=
  rfl

/-- Each algebraic stage inclusion is injective. -/
theorem stageι_injective (n : ℕ) :
    Function.Injective (stageι n : stage n → colimitCarrier) := by
  rintro ⟨q, v⟩ ⟨r, w⟩ h
  have hq := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  change Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm v) =
    Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm w) at hv
  exact Prod.ext hq (Finsupp.equivFunOnFinite.symm.injective
    (Finsupp.embDomain_injective Fin.valEmbedding hv))

/-- The algebraic stage inclusions commute with zero-padding successor maps. -/
theorem stageι_comp_stageTransitionHom (n : ℕ) :
    (stageι (n + 1)).comp (stageTransitionHom n) = stageι n := by
  apply AddMonoidHom.ext
  rintro ⟨q, v⟩
  apply Prod.ext
  · rfl
  · change Finsupp.embDomain Fin.valEmbedding
        (Finsupp.equivFunOnFinite.symm
          (Finsupp.embDomain Fin.castSuccEmb (Finsupp.equivFunOnFinite.symm v))) =
      Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm v)
    rw [Finsupp.equivFunOnFinite_symm_coe, ← Finsupp.embDomain_trans_apply]
    rfl

/-- The colimit topology of `system` in topological spaces: the final topology of the
stage inclusions. -/
@[implicit_reducible]
def spaceColimitTopology : TopologicalSpace colimitCarrier :=
  ⨆ n, coinduced (stageι n : stage n → colimitCarrier) inferInstance

/-- The colimit topology of `system` in topological groups: the finest additive group
topology making every stage inclusion continuous. -/
def groupColimitTopology : AddGroupTopology colimitCarrier :=
  sInf { t : AddGroupTopology colimitCarrier |
    ∀ n, Continuous[inferInstance, t.toTopologicalSpace] (stageι n) }

/-- A set is open in the space-colimit topology if and only if every stage preimage is
open. -/
theorem isOpen_spaceColimitTopology_iff (U : Set colimitCarrier) :
    IsOpen[spaceColimitTopology] U ↔
      ∀ n, IsOpen ((stageι n : stage n → colimitCarrier) ⁻¹' U) :=
  isOpen_iSup_iff

/-- Each stage inclusion is continuous for the space-colimit topology. -/
theorem continuous_stageι_spaceColimitTopology (n : ℕ) :
    Continuous[inferInstance, spaceColimitTopology] (stageι n) := by
  exact continuous_iSup_rng (i := n) continuous_coinduced_rng

/-- Each stage inclusion is continuous for the group-colimit topology. -/
theorem continuous_stageι_groupColimitTopology (n : ℕ) :
    Continuous[inferInstance, groupColimitTopology.toTopologicalSpace] (stageι n) := by
  change Continuous[inferInstance,
    sInf (AddGroupTopology.toTopologicalSpace ''
      {t : AddGroupTopology colimitCarrier | ∀ m, Continuous[inferInstance,
        t.toTopologicalSpace] (stageι m)})] (stageι n)
  rw [continuous_sInf_rng]
  rintro _ ⟨t, ht, rfl⟩
  exact ht n

/-- `colimitCarrier` bundled with the topological-space colimit topology. -/
def spaceColimit : TopCat.{0} :=
  @TopCat.of colimitCarrier spaceColimitTopology

/-- The topological inclusion of stage `n` into the space-colimit. -/
def spaceι (n : ℕ) : stageSpace n ⟶ spaceColimit :=
  @TopCat.ofHom (stage n) colimitCarrier inferInstance spaceColimitTopology <|
    @ContinuousMap.mk (stage n) colimitCarrier inferInstance spaceColimitTopology
      (stageι n) (continuous_stageι_spaceColimitTopology n)

/-- The topological cocone legs commute with successor maps. -/
theorem spaceι_naturality (n : ℕ) :
    system.map (homOfLE (n.le_add_right 1)) ≫ spaceι (n + 1) =
      spaceι n ≫ ((Functor.const ℕ).obj spaceColimit).map (homOfLE (n.le_add_right 1)) :=
  by
    rw [show system.map (homOfLE (n.le_add_right 1)) = stageTransition n from
      Functor.ofSequence_map_homOfLE_succ stageTransition n]
    ext x
    exact DFunLike.congr_fun (stageι_comp_stageTransitionHom n) x

/-- The sequential cocone on `system` with apex `spaceColimit`. -/
def spaceCocone : Cocone system where
  pt := spaceColimit
  ι := NatTrans.ofSequence spaceι spaceι_naturality

/-- The space-colimit topology does not make `colimitCarrier` a topological group. -/
theorem not_isTopologicalAddGroup_spaceColimitTopology :
    ¬ @IsTopologicalAddGroup colimitCarrier spaceColimitTopology _ := by
  classical
  -- Distances to irrational poles are positive on ℚ. Poles approaching zero
  -- obstruct continuity of addition, as do the cosine bounds in Stacks Tag 0B2Z.
  let a : ℕ → ℝ := fun j => Real.sqrt 2 / ((j + 1 : ℕ) : ℝ)
  have ha (j : ℕ) : Irrational (a j) :=
    irrational_sqrt_two.div_natCast (Nat.succ_ne_zero j)
  have hgap (j : ℕ) (q : ℚ) : 0 < |(q : ℝ) - a j| :=
    abs_pos.mpr (sub_ne_zero.mpr ((ha j).ne_rat q).symm)
  have hcoord (n : ℕ) (x : stage n) (i : Fin (n + 1)) :
      (stageι n x).2 i.val = x.2 i :=
    Finsupp.embDomain_apply_self Fin.valEmbedding _ i
  have htail (n : ℕ) (x : stage n) (j : ℕ) (hj : ¬ j < n + 1) :
      (stageι n x).2 j = 0 := by
    apply Finsupp.embDomain_notin_range
    rintro ⟨i, hi⟩
    exact hj (hi ▸ i.isLt)
  let U : Set colimitCarrier := {x | ∀ j, |x.2 j| < |(x.1 : ℝ) - a j|}
  have hU : IsOpen[spaceColimitTopology] U := by
    apply (isOpen_spaceColimitTopology_iff U).2
    intro n
    have heq : (stageι n : stage n → colimitCarrier) ⁻¹' U =
        ⋂ i : Fin (n + 1), {x : stage n | |x.2 i| < |(x.1 : ℝ) - a i.val|} := by
      ext x
      change (∀ j, |(stageι n x).2 j| < |(x.1 : ℝ) - a j|) ↔ _
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hx i
        simpa only [hcoord n x i] using hx i.val
      · intro hx j
        by_cases hj : j < n + 1
        · simpa only [hcoord n x ⟨j, hj⟩] using hx ⟨j, hj⟩
        · rw [htail n x j hj, abs_zero]
          exact hgap j x.1
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have hU0 : (0 : colimitCarrier) ∈ U := by
    intro j
    simpa using hgap j 0
  have hrat (n : ℕ) (q : ℚ) : stageι n (q, 0) = (q, 0) := by
    apply Prod.ext
    · rfl
    · change Finsupp.embDomain Fin.valEmbedding
        ((Finsupp.addEquivFunOnFinite).symm 0) = 0
      simp
  intro hG
  letI : TopologicalSpace colimitCarrier := spaceColimitTopology
  letI : IsTopologicalAddGroup colimitCarrier := hG
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half (hU.mem_nhds hU0)
  have hqcont : Continuous (fun q : ℚ => stageι 0 (q, 0)) :=
    (continuous_stageι_spaceColimitTopology 0).comp (by fun_prop)
  have hVq : (fun q : ℚ => stageι 0 (q, 0)) ⁻¹' V ∈ 𝓝 (0 : ℚ) := by
    apply hqcont.continuousAt.preimage_mem_nhds
    change V ∈ 𝓝 (stageι 0 (0 : stage 0))
    rw [map_zero]
    exact hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hVq
  obtain ⟨j, hj⟩ := exists_nat_gt (Real.sqrt 2 / ε)
  have haj0 : 0 < a j := by
    dsimp [a]
    positivity
  have haj : a j < ε := by
    have h := (div_lt_iff₀ hε).1 hj
    dsimp [a]
    apply (div_lt_iff₀ (by positivity : 0 < ((j + 1 : ℕ) : ℝ))).2
    push_cast
    nlinarith
  have hrcont : Continuous (fun r : ℝ => stageι j (0, fun _ => r)) :=
    (continuous_stageι_spaceColimitTopology j).comp (by fun_prop)
  have hVr : (fun r : ℝ => stageι j (0, fun _ => r)) ⁻¹' V ∈ 𝓝 (0 : ℝ) := by
    apply hrcont.continuousAt.preimage_mem_nhds
    change V ∈ 𝓝 (stageι j (0 : stage j))
    rw [map_zero]
    exact hV
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hVr
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  have hrv : stageι j (0, fun _ => r) ∈ V := by
    apply hδV
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hr, r] using half_lt_self hδ
  have hS : {t : ℝ | |t| < ε ∧ |t - a j| < r} ∈ 𝓝 (a j) := by
    apply Filter.inter_mem
    · apply (isOpen_lt continuous_abs continuous_const).mem_nhds
      change |a j| < ε
      rwa [abs_of_pos haj0]
    · apply (isOpen_lt (continuous_id.sub continuous_const).abs continuous_const).mem_nhds
      change |a j - a j| < r
      simpa only [sub_self, abs_zero] using hr
  obtain ⟨q, hq, hqclose⟩ := Rat.denseRange_cast.mem_nhds hS
  have hqv : stageι 0 (q, 0) ∈ V := by
    apply hεV
    simpa [Metric.mem_ball, Rat.dist_eq] using hq
  have hsum := hVV _ hqv _ hrv
  have hval : (stageι j (0, fun _ => r)).2 j = r :=
    hcoord j _ ⟨j, Nat.lt_succ_self j⟩
  have hfst : (stageι j (0, fun _ => r)).1 = 0 := by
    rw [stageι_apply]
  have hbad := hsum j
  rw [hrat] at hbad
  have hbad' : r < |(q : ℝ) - a j| := by
    simpa only [Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd, hfst, hval,
      zero_add, add_zero, abs_of_pos hr] using hbad
  exact (not_lt_of_ge hqclose.le) hbad'

/-- The specified space cocone satisfies the categorical colimit universal property. -/
theorem nonempty_isColimit_spaceCocone : Nonempty (IsColimit spaceCocone) := by
  have hsurj (x : colimitCarrier) : ∃ n v, stageι n v = x := by
    rcases x with ⟨q, f⟩
    let n := f.support.sup id
    have hf : f ∈ Set.range (Finsupp.embDomain
        (Fin.valEmbedding : Fin (n + 1) ↪ ℕ)) := by
      apply (Finsupp.mem_range_embDomain_iff _ _).2
      intro i hi
      exact ⟨⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩, rfl⟩
    obtain ⟨v, hv⟩ := hf
    refine ⟨n, (q, v), ?_⟩
    rw [stageι_apply, Finsupp.equivFunOnFinite_symm_coe, hv]
  let c := (forget TopCat).mapCocone spaceCocone
  have hc : IsColimit c := by
    apply Types.FilteredColimit.isColimitOf (system ⋙ forget TopCat) c
    · intro x
      obtain ⟨n, v, hv⟩ := hsurj x
      exact ⟨n, v, hv.symm⟩
    · intro i j x y h
      let k := max i j
      let f : i ⟶ k := homOfLE (le_max_left i j)
      let g : j ⟶ k := homOfLE (le_max_right i j)
      refine ⟨k, f, g, ?_⟩
      apply stageι_injective k
      have hx : stageι k (system.map f x) = stageι i x :=
        ConcreteCategory.congr_hom (spaceCocone.w f) x
      have hy : stageι k (system.map g y) = stageι j y :=
        ConcreteCategory.congr_hom (spaceCocone.w g) y
      exact hx.trans (h.trans hy.symm)
  apply (TopCat.nonempty_isColimit_iff_eq_coinduced spaceCocone hc).2
  rfl

/-- The final space topology and the finest admissible additive group topology differ
on the rational-times-finite-support real carrier. -/
theorem spaceColimitTopology_ne_groupColimitTopology :
    spaceColimitTopology ≠ groupColimitTopology.toTopologicalSpace := by
  intro h
  apply not_isTopologicalAddGroup_spaceColimitTopology
  rw [h]
  exact groupColimitTopology.toIsTopologicalAddGroup

end

end TopCat.Counterexample.NatAddGroupColimit
