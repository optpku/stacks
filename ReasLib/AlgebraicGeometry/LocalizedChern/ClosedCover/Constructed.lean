/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward.Composition
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Actual closed-cover cap descent

On a base-changed closed cover take the sum of the two proper pushforwards.
The operation on its source is (alpha1,alpha2) ↦ ambient.cap(alpha2). It
descends through this specified surjection because the intersection action
vanishes. No bivariant class is chosen from an existence or IsResult predicate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern.Constructed

/-- Restrict coefficients to a closed member and a specified set of its points.
The degree filter makes this a cycle of the required degree without choosing
any point or cycle. For the relative gradings of a closed immersion it is inert
on nonzero coefficients of the input cycle. -/
def memberCycle {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsClosedImmersion j]
    (dY : Y → ℤ) (dZ : Z → ℤ) (k : ℤ) (P : Y → Prop)
    (c : CycleGroup Z dZ k) : CycleGroup Y dY k := by
  classical
  refine ⟨{
    toFun := fun y ↦ if dY y = k ∧ P y then c.1 (j y) else 0
    supportWithinDomain' := fun _ _ ↦ Set.mem_univ _
    supportLocallyFiniteWithinDomain' := ?_ }, ?_⟩
  · intro y _
    obtain ⟨t, ht, hfinite⟩ := c.1.locallyFiniteSupport (j y)
    refine ⟨j ⁻¹' t, j.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    apply (hfinite.preimage j.isClosedEmbedding.injective.injOn).subset
    intro x hx
    refine ⟨hx.1, ?_⟩
    change c.1 (j x) ≠ 0
    by_cases h : dY x = k ∧ P x
    · simpa only [Function.mem_support, if_pos h] using hx.2
    · exact (hx.2 (if_neg h)).elim
  · apply (AlgebraicCycle.mem_dimensionSubgroup dY k _).2
    intro y hy
    change (if dY y = k ∧ P y then c.1 (j y) else 0) ≠ 0 at hy
    by_cases h : dY y = k ∧ P y
    · exact h.1
    · exact (hy (if_neg h)).elim

open scoped Classical in
/-- The member cycle has the input coefficient at precisely the selected points. -/
theorem memberCycle_apply {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsClosedImmersion j]
    (dY : Y → ℤ) (dZ : Z → ℤ) (k : ℤ) (P : Y → Prop)
    (c : CycleGroup Z dZ k) (y : Y) :
    (memberCycle j dY dZ k P c).1 y =
      if dY y = k ∧ P y then c.1 (j y) else 0 := by
  classical
  rfl

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
  {X : Over S} [LocallyOfFiniteType X.hom]
  {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
  [hc₁ : IsClosedImmersion i₁] [hc₂ : IsClosedImmersion i₂]

abbrev source₂ : Over S := Over.mk (i₂ ≫ X.hom)

variable (p : ℤ) (ambient : BivariantClass δ (𝟙 (source₂ i₂)) p)

/-- The ambient operation vanishes on every actual test map factoring through
both cover members. This is the source's intersection-vanishing hypothesis,
not a desired property imposed on a newly supplied localized answer. -/
def IntersectionVanishes : Prop :=
  ∀ {V : Over S} [LocallyOfFiniteType V.hom]
    (v₂ : V ⟶ source₂ i₂) [LocallyOfFiniteType v₂.left]
    (v₁ : V.left ⟶ X₁), v₂.left ≫ i₂ = v₁ ≫ i₁ →
      ∀ k : ℤ, ambient.cap v₂ (𝟙 V) v₂ IsPullback.of_id_snd k = 0

variable {V V₂ : Over S} [LocallyOfFiniteType V.hom] [LocallyOfFiniteType V₂.hom]
  (a : V₂ ⟶ source₂ i₂) (j₂ : V₂ ⟶ V) (g : V ⟶ X)
  [LocallyOfFiniteType g.left] (square : IsPullback a.left j₂.left i₂ g.left)

/-- The actual first member of the base-changed cover. -/
def member₁ : Over S := Over.mk (pullback.snd i₁ g.left ≫ V.hom)

def inclusion₁ : member₁ i₁ g ⟶ V := Over.homMk (pullback.snd i₁ g.left)

include hc₁ in
instance member₁_finiteType : LocallyOfFiniteType (member₁ i₁ g).hom := by
  change LocallyOfFiniteType (pullback.snd i₁ g.left ≫ V.hom)
  infer_instance

include hc₁ in
instance inclusion₁_proper : IsProper (inclusion₁ i₁ g).left := by
  change IsProper (pullback.snd i₁ g.left)
  infer_instance

include square hc₂ in
theorem second_proper : IsProper j₂.left := by
  letI : IsClosedImmersion j₂.left := MorphismProperty.of_isPullback square hc₂
  infer_instance

include square in
theorem second_to_source_finiteType : LocallyOfFiniteType a.left := by
  exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) square.flip inferInstance

/-- The fixed closed-cover surjection, using both actual proper pushforwards. -/
def sumPushforward (k : ℤ) :
    (RelativeChow δ (member₁ i₁ g) k × RelativeChow δ V₂ k) →+ RelativeChow δ V k := by
  letI := second_proper i₂ a j₂ g square
  exact (ChowGroup.map δ (member₁ i₁ g) V (inclusion₁ i₁ g) k).coprod
    (ChowGroup.map δ V₂ V j₂ k)

/-- The specified operation before descending: zero on the first member,
the given ambient operation on the second member. -/
def pairCap (k : ℤ) :
    (RelativeChow δ (member₁ i₁ g) k × RelativeChow δ V₂ k) →+ RelativeChow δ V₂ (k - p) := by
  letI := second_to_source_finiteType i₂ a j₂ g square
  exact (ambient.cap a (𝟙 V₂) a IsPullback.of_id_snd k).comp (AddMonoidHom.snd _ _)

/-- Split a cycle on the actual base-changed closed cover. Coefficients in
the first member go to that member; all remaining coefficients go to the
second member. In particular intersection coefficients are counted only once. -/
def cycleDecomposition (k : ℤ)
    (c : CycleGroup V.left (V.hom.relativeDimensionFunction δ) k) :
    CycleGroup (member₁ i₁ g).left ((member₁ i₁ g).hom.relativeDimensionFunction δ) k ×
      CycleGroup V₂.left (V₂.hom.relativeDimensionFunction δ) k := by
  -- These are the closed immersions of the displayed pullback cover, so their
  -- injective point maps preserve local finiteness in memberCycle.
  letI : IsClosedImmersion (inclusion₁ i₁ g).left := by
    change IsClosedImmersion (pullback.snd i₁ g.left)
    infer_instance
  letI : IsClosedImmersion j₂.left :=
    MorphismProperty.of_isPullback square hc₂
  exact
    (memberCycle (inclusion₁ i₁ g).left
      ((member₁ i₁ g).hom.relativeDimensionFunction δ)
      (V.hom.relativeDimensionFunction δ) k (fun _ ↦ True) c,
    memberCycle j₂.left (V₂.hom.relativeDimensionFunction δ)
      (V.hom.relativeDimensionFunction δ) k
      (fun x ↦ j₂.left x ∉ Set.range (inclusion₁ i₁ g).left) c)

/-- A concrete pair of Chow preimages. The only representative selection is
Quotient.out for the actual cycle quotient; its existence is proved by the
quotient API. Neither closed-cover surjectivity nor chowClass_surjective is
used to select data. -/
def chowPreimage (k : ℤ) (α : RelativeChow δ V k) :
    RelativeChow δ (member₁ i₁ g) k × RelativeChow δ V₂ k :=
  let c := cycleDecomposition δ i₁ i₂ a j₂ g square k (Quotient.out α)
  (@chowClass (member₁ i₁ g).left
      (LocallyOfFiniteType.isLocallyNoetherian (member₁ i₁ g).hom)
      ((member₁ i₁ g).hom.relativeDimensionFunction δ) inferInstance k c.1,
    @chowClass V₂.left (LocallyOfFiniteType.isLocallyNoetherian V₂.hom)
      (V₂.hom.relativeDimensionFunction δ) inferInstance k c.2)

variable (cover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
  (vanishing : IntersectionVanishes δ i₁ i₂ p ambient)

include cover in
/-- Closed immersions preserve the relative grading and have residue degree
one. Thus the coefficient split covers every point, and passage to the Chow
quotient gives a right inverse to the specified sum map. -/
theorem sumPushforward_rightInverse (k : ℤ) :
    Function.RightInverse (chowPreimage δ i₁ i₂ a j₂ g square k)
      (sumPushforward δ i₁ i₂ a j₂ g square k) := by
  sorry

include cover in
/-- The concrete sum map is onto with the explicitly constructed Chow preimages. -/
theorem sumPushforward_surjective (k : ℤ) :
    Function.Surjective (sumPushforward δ i₁ i₂ a j₂ g square k) := by
  intro α
  exact ⟨chowPreimage δ i₁ i₂ a j₂ g square k α,
    sumPushforward_rightInverse δ i₁ i₂ a j₂ g square cover k α⟩

include cover vanishing in
/-- Signed intersection pushforward generates the kernel, and the given
ambient operation vanishes on those intersection contributions. -/
theorem pairCap_kills_kernel (k : ℤ) :
    (sumPushforward δ i₁ i₂ a j₂ g square k).ker ≤
      (pairCap δ i₁ i₂ p ambient a j₂ g square k).ker := by
  sorry

/-- Descent using the explicit cycle-based Chow preimages. The right-inverse
and kernel laws prove that pairCap is independent of the representative. -/
def descendedCap (k : ℤ) : RelativeChow δ V k →+ RelativeChow δ V₂ (k - p) :=
  (sumPushforward δ i₁ i₂ a j₂ g square k).liftOfRightInverse
    (chowPreimage δ i₁ i₂ a j₂ g square k)
    (sumPushforward_rightInverse δ i₁ i₂ a j₂ g square cover k)
    ⟨pairCap δ i₁ i₂ p ambient a j₂ g square k,
      pairCap_kills_kernel δ i₁ i₂ p ambient a j₂ g square cover vanishing k⟩

/-- Evaluation uses the displayed cycle-based Chow decomposition. -/
theorem descendedCap_apply (k : ℤ) (α : RelativeChow δ V k) :
    descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k α =
      pairCap δ i₁ i₂ p ambient a j₂ g square k
        (chowPreimage δ i₁ i₂ a j₂ g square k α) := rfl

/-- Quotient evaluation recovers the exact operation on every pair of input classes. -/
theorem descendedCap_sum (k : ℤ)
    (x : RelativeChow δ (member₁ i₁ g) k × RelativeChow δ V₂ k) :
    descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k
      (sumPushforward δ i₁ i₂ a j₂ g square k x) =
        pairCap δ i₁ i₂ p ambient a j₂ g square k x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- On the second cover member, descent recovers the ambient action. -/
theorem descendedCap_source_pushforward [IsProper j₂.left] (k : ℤ)
    (α₂ : RelativeChow δ V₂ k) :
    descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k
      (ChowGroup.map δ V₂ V j₂ k α₂) =
        (pairCap δ i₁ i₂ p ambient a j₂ g square k) (0, α₂) := by
  simpa [sumPushforward] using
    descendedCap_sum δ i₁ i₂ p ambient a j₂ g square cover vanishing k (0, α₂)

/-- Descent kills proper pushforwards from any test scheme factoring through
the first member. The factorization through the displayed pullback is canonical. -/
theorem descendedCap_other_pushforward
    {W : Over S} [LocallyOfFiniteType W.hom] (h : W ⟶ V) [IsProper h.left]
    (v₁ : W.left ⟶ X₁) (comm : v₁ ≫ i₁ = h.left ≫ g.left)
    (k : ℤ) (α₁ : RelativeChow δ W k) :
    descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k
      (ChowGroup.map δ W V h k α₁) = 0 := by
  let t : W ⟶ member₁ i₁ g :=
    Over.homMk (pullback.lift v₁ h.left comm) (by
      change pullback.lift v₁ h.left comm ≫
        (pullback.snd i₁ g.left ≫ V.hom) = W.hom
      simpa only [pullback.lift_snd_assoc] using h.w)
  have ht : t ≫ inclusion₁ i₁ g = h := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd v₁ h.left comm
  haveI : IsProper (t.left ≫ (inclusion₁ i₁ g).left) := by
    change IsProper (t ≫ inclusion₁ i₁ g).left
    rw [ht]
    infer_instance
  haveI : IsProper t.left := IsProper.of_comp _ (inclusion₁ i₁ g).left
  have hmap : ChowGroup.map δ W V h k α₁ =
      ChowGroup.map δ (member₁ i₁ g) V (inclusion₁ i₁ g) k
        (ChowGroup.map δ W (member₁ i₁ g) t k α₁) := by
    have hc := congrArg (fun f ↦ f α₁)
      (ChowGroup.map_comp δ W (member₁ i₁ g) V t (inclusion₁ i₁ g) k)
    simpa only [AddMonoidHom.comp_apply, ht] using hc.symm
  rw [hmap]
  simpa [sumPushforward, pairCap] using
    descendedCap_sum δ i₁ i₂ p ambient a j₂ g square cover vanishing k
      (ChowGroup.map δ W (member₁ i₁ g) t k α₁, 0)

/-- The constructed cap family on every actual cartesian base change. -/
def capFamily : BivariantClass.CapFamily δ
    (Over.homMk i₂ : source₂ i₂ ⟶ X) p :=
  fun {_ _} _ _ a j₂ g _ square k =>
    descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k

theorem capFamily_proper : BivariantClass.CompatibleWithProperPushforward δ
    (capFamily δ i₁ i₂ p ambient cover vanishing) := by
  intro V₂ V W₂ W _ _ _ _ a j₂ g _ square t j₂' h inner _ _ k α
  change IsPullback a.left j₂.left i₂ g.left at square
  letI := second_proper i₂ a j₂ g square
  letI := second_to_source_finiteType i₂ a j₂ g square
  let square' : IsPullback (t ≫ a).left j₂'.left i₂ (h ≫ g).left :=
    inner.paste_horiz square
  letI := second_proper i₂ (t ≫ a) j₂' (h ≫ g) square'
  haveI : IsProper (inclusion₁ i₁ (h ≫ g) ≫ h).left := by
    change IsProper ((inclusion₁ i₁ (h ≫ g)).left ≫ h.left)
    infer_instance
  haveI : IsProper (j₂' ≫ h).left := by
    change IsProper (j₂'.left ≫ h.left)
    infer_instance
  haveI : IsProper (t ≫ j₂).left := by
    change IsProper (t.left ≫ j₂.left)
    infer_instance
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ :=
    sumPushforward_surjective δ i₁ i₂ (t ≫ a) j₂' (h ≫ g) square' cover k α
  have hfirst :
      descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k
        (ChowGroup.map δ W V h k
          (ChowGroup.map δ (member₁ i₁ (h ≫ g)) W (inclusion₁ i₁ (h ≫ g)) k α₁)) = 0 := by
    have hc := congrArg (fun f ↦ f α₁)
      (ChowGroup.map_comp δ (member₁ i₁ (h ≫ g)) W V (inclusion₁ i₁ (h ≫ g)) h k)
    rw [show ChowGroup.map δ W V h k
        (ChowGroup.map δ (member₁ i₁ (h ≫ g)) W (inclusion₁ i₁ (h ≫ g)) k α₁) =
        ChowGroup.map δ (member₁ i₁ (h ≫ g)) V (inclusion₁ i₁ (h ≫ g) ≫ h) k α₁
      from hc]
    apply descendedCap_other_pushforward δ i₁ i₂ p ambient a j₂ g square cover vanishing
      (inclusion₁ i₁ (h ≫ g) ≫ h) (pullback.fst i₁ (h ≫ g).left) _ k α₁
    change pullback.fst i₁ (h.left ≫ g.left) ≫ i₁ =
      (pullback.snd i₁ (h.left ≫ g.left) ≫ h.left) ≫ g.left
    simpa only [Category.assoc] using
      (pullback.condition (f := i₁) (g := h.left ≫ g.left))
  have ht : j₂' ≫ h = t ≫ j₂ := by
    apply Over.OverMorphism.ext
    exact inner.w.symm
  have hsecond :
      ChowGroup.map δ W V h k (ChowGroup.map δ W₂ W j₂' k α₂) =
        ChowGroup.map δ V₂ V j₂ k (ChowGroup.map δ W₂ V₂ t k α₂) := by
    calc
      _ = ChowGroup.map δ W₂ V (j₂' ≫ h) k α₂ := congrArg (fun f ↦ f α₂)
        (ChowGroup.map_comp δ W₂ W V j₂' h k)
      _ = ChowGroup.map δ W₂ V (t ≫ j₂) k α₂ := by simp only [ht]
      _ = _ := (congrArg (fun f ↦ f α₂)
        (ChowGroup.map_comp δ W₂ V₂ V t j₂ k)).symm
  have hamb := ambient.map_proper a (𝟙 V₂) a IsPullback.of_id_snd
    t (𝟙 W₂) t IsPullback.of_id_snd k α₂
  change descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k _ =
    ChowGroup.map δ W₂ V₂ t (k - p)
      (descendedCap δ i₁ i₂ p ambient (t ≫ a) j₂' (h ≫ g) square' cover vanishing k
        (sumPushforward δ i₁ i₂ (t ≫ a) j₂' (h ≫ g) square' k (α₁, α₂)))
  rw [descendedCap_sum]
  change descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k
      (ChowGroup.map δ W V h k
        (ChowGroup.map δ (member₁ i₁ (h ≫ g)) W (inclusion₁ i₁ (h ≫ g)) k α₁ +
          ChowGroup.map δ W₂ W j₂' k α₂)) =
    ChowGroup.map δ W₂ V₂ t (k - p)
      (ambient.cap (t ≫ a) (𝟙 W₂) (t ≫ a) IsPullback.of_id_snd k α₂)
  rw [map_add, map_add, hfirst, zero_add, hsecond,
    descendedCap_source_pushforward δ i₁ i₂ p ambient a j₂ g square cover vanishing]
  exact hamb

theorem capFamily_flat : BivariantClass.CompatibleWithFlatPullback δ
    (capFamily δ i₁ i₂ p ambient cover vanishing) := by
  sorry

theorem capFamily_gysin : BivariantClass.CompatibleWithCartierGysin δ
    (capFamily δ i₁ i₂ p ambient cover vanishing) := by
  sorry

/-- A real bivariant class record, whose cap field is the specified quotient descent. -/
def localized : BivariantClass δ (Over.homMk i₂ : source₂ i₂ ⟶ X) p where
  cap := capFamily δ i₁ i₂ p ambient cover vanishing
  map_proper := capFamily_proper δ i₁ i₂ p ambient cover vanishing
  pullback_flat := capFamily_flat δ i₁ i₂ p ambient cover vanishing
  gysin_cartier := capFamily_gysin δ i₁ i₂ p ambient cover vanishing

theorem localized_cap (k : ℤ) (α : RelativeChow δ V k) :
    (localized δ i₁ i₂ p ambient cover vanishing).cap a j₂ g square k α =
      descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k α := rfl

/-- The two source cap laws for this concrete descent. Their proof reduces
to descendedCap_sum at (0,alpha2) and (alpha1,0), respectively. -/
theorem localized_spec : BivariantClass.IsLocalizedExtension δ X i₁ i₂ p ambient
    (localized δ i₁ i₂ p ambient cover vanishing) := by
  constructor
  · intro Y Y₂ _ _ g _ j₂ _ a _ square k α₂
    change descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k
      (ChowGroup.map δ Y₂ Y j₂ k α₂) = _
    exact descendedCap_source_pushforward δ i₁ i₂ p ambient a j₂ g square cover vanishing k α₂
  · intro Y Y₁ Y₂ _ _ _ g _ j₁ _ g₁ square₁ j₂ a square₂ k α₁
    exact descendedCap_other_pushforward δ i₁ i₂ p ambient a j₂ g square₂ cover vanishing
      j₁ g₁.left square₁.w k α₁

end AlgebraicGeometry.LocalizedChern.Constructed
