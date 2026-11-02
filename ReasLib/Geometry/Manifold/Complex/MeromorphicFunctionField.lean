/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.RingQuot
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import ReasLib.Geometry.Manifold.Complex.Nontrivial

@[expose] public section

/-!
# Meromorphic Function Fields

For a connected complex one-manifold, this module constructs the field of meromorphic functions
modulo codiscrete equality and exposes the representative-level API used by function-field
arguments.
-/

open scoped Manifold Topology

universe u

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

-- Local instance justification (instance diamond): `MeromorphicAt.mul` uses the additive normed
-- group projected from its normed algebra, so chart expressions must use that same instance.
noncomputable local instance : NormedAddCommGroup ℂ :=
  NonUnitalNormedRing.toNormedAddCommGroup

-- Local instance justification (instance diamond): `MeromorphicAt.mul` uses the normed-space
-- structure induced by `NormedAlgebra ℂ ℂ`, so the chart expressions must use that same instance.
noncomputable local instance : NormedSpace ℂ ℂ := NormedAlgebra.toNormedSpace ℂ

/-- The coordinate expression of a representative in the extended chart at a point. -/
noncomputable abbrev MeromorphicFunctionField.chartExpression
    (x : X) (f : X → ℂ) : ℂ → ℂ :=
  writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f

/-- A representative for the meromorphic function field is meromorphic if, in every complex
chart, its coordinate expression is meromorphic at the charted point. -/
def MeromorphicFunctionField.IsMeromorphic (f : X → ℂ) : Prop :=
  ∀ x, MeromorphicAt (MeromorphicFunctionField.chartExpression X x f) (extChartAt 𝓘(ℂ) x x)

namespace MeromorphicFunctionField.IsMeromorphic

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Constant functions are meromorphic representatives for the meromorphic function field. -/
theorem const (c : ℂ) :
    MeromorphicFunctionField.IsMeromorphic X (fun _ ↦ c) := by
  intro x
  change MeromorphicAt (fun _ : ℂ ↦ c) ((chartAt ℂ x) x)
  exact MeromorphicAt.const c ((chartAt ℂ x) x)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Sums of meromorphic representatives are meromorphic. -/
theorem add {f g : X → ℂ} (hf : MeromorphicFunctionField.IsMeromorphic X f)
    (hg : MeromorphicFunctionField.IsMeromorphic X g) :
    MeromorphicFunctionField.IsMeromorphic X (f + g) := by
  intro x
  convert (hf x).add (hg x) using 1
  ext z
  rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Products of meromorphic representatives are meromorphic. -/
theorem mul {f g : X → ℂ} (hf : MeromorphicFunctionField.IsMeromorphic X f)
    (hg : MeromorphicFunctionField.IsMeromorphic X g) :
    MeromorphicFunctionField.IsMeromorphic X (f * g) := by
  intro x
  convert (hf x).mul (hg x) using 1
  · rfl
  · rfl
  · ext z
    rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Pointwise inverses of meromorphic representatives are meromorphic. -/
theorem inv {f : X → ℂ} (hf : MeromorphicFunctionField.IsMeromorphic X f) :
    MeromorphicFunctionField.IsMeromorphic X f⁻¹ := by
  intro x
  change MeromorphicAt ((MeromorphicFunctionField.chartExpression X x f)⁻¹) ((chartAt ℂ x) x)
  simpa [MeromorphicFunctionField.IsMeromorphic, MeromorphicFunctionField.chartExpression] using (hf x).inv

end MeromorphicFunctionField.IsMeromorphic

/-- Meromorphic representatives as a subalgebra of all complex-valued functions. -/
def MeromorphicFunctionField.Representative.subalgebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | MeromorphicFunctionField.IsMeromorphic X f}
  zero_mem' := by
    exact MeromorphicFunctionField.IsMeromorphic.const X 0
  add_mem' := fun hf hg ↦ MeromorphicFunctionField.IsMeromorphic.add X hf hg
  one_mem' := by
    exact MeromorphicFunctionField.IsMeromorphic.const X 1
  mul_mem' := fun hf hg ↦ MeromorphicFunctionField.IsMeromorphic.mul X hf hg
  algebraMap_mem' := by
    intro c x
    exact MeromorphicFunctionField.IsMeromorphic.const X c x

/-- Pointwise inversion on meromorphic representatives. -/
noncomputable instance MeromorphicFunctionField.Representative.instInv :
    Inv ↥(MeromorphicFunctionField.Representative.subalgebra X) where
  inv f := ⟨(f : X → ℂ)⁻¹, f.property.inv⟩

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The private inverse on representatives is pointwise inversion. -/
private theorem representative_inv_apply
    (f : ↥(MeromorphicFunctionField.Representative.subalgebra X)) (x : X) :
    ((f⁻¹ : ↥(MeromorphicFunctionField.Representative.subalgebra X)) : X → ℂ) x =
      ((f : X → ℂ) x)⁻¹ := by
  rfl

/-- Codiscrete equality as a congruence on meromorphic representatives. -/
def MeromorphicFunctionField.Representative.con :
    RingCon ↥(MeromorphicFunctionField.Representative.subalgebra X) where
  r f g := (f : X → ℂ) =ᶠ[Filter.codiscrete X] (g : X → ℂ)
  iseqv := ⟨fun f ↦ Filter.EventuallyEq.rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  add' := by
    intro a b c d hab hcd
    exact hab.add hcd
  mul' := by
    intro a b c d hab hcd
    exact hab.mul hcd

/-- The meromorphic function field `ℂ(X)`, realized as meromorphic representatives modulo
codiscrete equality, which forgets inessential point values at isolated poles. -/
def MeromorphicFunctionField := RingCon.Quotient (MeromorphicFunctionField.Representative.con X)

/-- The quotient construction supplies the commutative-ring structure on meromorphic classes. -/
noncomputable instance : CommRing (MeromorphicFunctionField X) :=
  inferInstanceAs (CommRing (RingCon.Quotient (MeromorphicFunctionField.Representative.con X)))

/-- Constants embed canonically into the ring of meromorphic classes. -/
noncomputable instance : Algebra ℂ (MeromorphicFunctionField X) :=
  inferInstanceAs (Algebra ℂ (RingCon.Quotient (MeromorphicFunctionField.Representative.con X)))

/-- The quotient class of a meromorphic representative in the meromorphic function field. -/
noncomputable def MeromorphicFunctionField.mk (f : X → ℂ)
    (hf : MeromorphicFunctionField.IsMeromorphic X f) : MeromorphicFunctionField X :=
  (↑(⟨f, hf⟩ : MeromorphicFunctionField.Representative.subalgebra X) :
    RingCon.Quotient (MeromorphicFunctionField.Representative.con X))

/-- Equality of meromorphic classes is exactly codiscrete equality of representatives. -/
theorem MeromorphicFunctionField.mk_eq_mk_iff {f g : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f}
    {hg : MeromorphicFunctionField.IsMeromorphic X g} :
    MeromorphicFunctionField.mk X f hf = MeromorphicFunctionField.mk X g hg ↔
      f =ᶠ[Filter.codiscrete X] g := by
  exact (MeromorphicFunctionField.Representative.con X).eq

/-- Prove a property of a meromorphic class by proving it for every meromorphic representative. -/
protected theorem MeromorphicFunctionField.inductionOn
    {P : MeromorphicFunctionField X → Prop} (a : MeromorphicFunctionField X)
    (h : ∀ f : X → ℂ, ∀ hf : MeromorphicFunctionField.IsMeromorphic X f,
      P (MeromorphicFunctionField.mk X f hf)) :
    P a := by
  refine Quotient.inductionOn a ?_
  intro f
  exact h f f.property

/-- The zero representative defines zero in the meromorphic function field. -/
@[simp]
theorem MeromorphicFunctionField.mk_zero :
    MeromorphicFunctionField.mk X 0
      (MeromorphicFunctionField.IsMeromorphic.const X 0) = 0 := by
  rfl

/-- The one representative defines one in the meromorphic function field. -/
@[simp]
theorem MeromorphicFunctionField.mk_one :
    MeromorphicFunctionField.mk X 1
      (MeromorphicFunctionField.IsMeromorphic.const X 1) = 1 := by
  rfl

/-- Taking quotient classes commutes with addition of meromorphic representatives. -/
@[simp]
theorem MeromorphicFunctionField.mk_add {f g : X → ℂ}
    (hf : MeromorphicFunctionField.IsMeromorphic X f)
    (hg : MeromorphicFunctionField.IsMeromorphic X g) :
    MeromorphicFunctionField.mk X (f + g)
      (MeromorphicFunctionField.IsMeromorphic.add X hf hg) =
      MeromorphicFunctionField.mk X f hf + MeromorphicFunctionField.mk X g hg := by
  rfl

/-- Taking quotient classes commutes with multiplication of meromorphic representatives. -/
@[simp]
theorem MeromorphicFunctionField.mk_mul {f g : X → ℂ}
    (hf : MeromorphicFunctionField.IsMeromorphic X f)
    (hg : MeromorphicFunctionField.IsMeromorphic X g) :
    MeromorphicFunctionField.mk X (f * g)
      (MeromorphicFunctionField.IsMeromorphic.mul X hf hg) =
      MeromorphicFunctionField.mk X f hf * MeromorphicFunctionField.mk X g hg := by
  rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Meromorphic representatives that agree on the codiscrete filter define the same element of
the meromorphic function field. -/
theorem MeromorphicFunctionField.mk_eq_mk_of_eventuallyEq {f g : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f}
    {hg : MeromorphicFunctionField.IsMeromorphic X g}
    (h : f =ᶠ[Filter.codiscrete X] g) :
    MeromorphicFunctionField.mk X f hf = MeromorphicFunctionField.mk X g hg := by
  change (↑(⟨f, hf⟩ : MeromorphicFunctionField.Representative.subalgebra X) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X)) =
    (↑(⟨g, hg⟩ : MeromorphicFunctionField.Representative.subalgebra X) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X))
  apply (RingCon.eq (MeromorphicFunctionField.Representative.con X)).mpr
  exact h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A meromorphic representative that is codiscretely zero defines zero in the meromorphic
function field. -/
theorem MeromorphicFunctionField.mk_eq_zero_of_eventuallyEq_zero {f : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f}
    (h : f =ᶠ[Filter.codiscrete X] 0) :
    MeromorphicFunctionField.mk X f hf = 0 := by
  change (↑(⟨f, hf⟩ : MeromorphicFunctionField.Representative.subalgebra X) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X)) =
    (↑(0 : MeromorphicFunctionField.Representative.subalgebra X) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X))
  apply (RingCon.eq (MeromorphicFunctionField.Representative.con X)).mpr
  exact h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A meromorphic representative that is codiscretely constant defines the corresponding
constant element of the meromorphic function field. -/
theorem MeromorphicFunctionField.mk_eq_algebraMap_of_eventuallyEq_const {f : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f} {c : ℂ}
    (h : f =ᶠ[Filter.codiscrete X] (fun _ ↦ c)) :
    MeromorphicFunctionField.mk X f hf = algebraMap ℂ (MeromorphicFunctionField X) c := by
  change (↑(⟨f, hf⟩ : MeromorphicFunctionField.Representative.subalgebra X) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X)) =
    (↑(algebraMap ℂ (MeromorphicFunctionField.Representative.subalgebra X) c) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X))
  apply (RingCon.eq (MeromorphicFunctionField.Representative.con X)).mpr
  exact h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- If a representative gives a constant element of the meromorphic function field, then it is
codiscretely equal to that constant. -/
theorem MeromorphicFunctionField.eventuallyEq_const_of_mk_eq_algebraMap {f : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f} {c : ℂ}
    (h : MeromorphicFunctionField.mk X f hf = algebraMap ℂ (MeromorphicFunctionField X) c) :
    f =ᶠ[Filter.codiscrete X] (fun _ ↦ c) := by
  change (↑(⟨f, hf⟩ : MeromorphicFunctionField.Representative.subalgebra X) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X)) =
    (↑(algebraMap ℂ (MeromorphicFunctionField.Representative.subalgebra X) c) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X)) at h
  exact (RingCon.eq (MeromorphicFunctionField.Representative.con X)).mp h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A representative that is not codiscretely constant gives a nonconstant element of the
meromorphic function field. -/
theorem MeromorphicFunctionField.mk_notMem_range_algebraMap_of_forall_not_eventuallyEq_const
    {f : X → ℂ} {hf : MeromorphicFunctionField.IsMeromorphic X f}
    (h : ∀ c : ℂ, ¬ f =ᶠ[Filter.codiscrete X] (fun _ ↦ c)) :
    MeromorphicFunctionField.mk X f hf ∉
      Set.range (algebraMap ℂ (MeromorphicFunctionField X)) := by
  rintro ⟨c, hc⟩
  exact h c <|
    MeromorphicFunctionField.eventuallyEq_const_of_mk_eq_algebraMap X hc.symm

end

scoped[MeromorphicFunctionField] notation:max "ℂ(" X ")" => MeromorphicFunctionField X

open scoped MeromorphicFunctionField

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

omit [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- The chosen chart maps punctured neighborhoods to punctured neighborhoods. -/
private theorem chartAt_tendsto_punctured_nhds (x : X) :
    Filter.Tendsto (chartAt ℂ x) (𝓝[≠] x) (𝓝[≠] ((chartAt ℂ x) x)) := by
  -- Continuity gives the ordinary limit, and local injectivity keeps away from the base point.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (chartAt ℂ x) ?_ ?_
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).tendsto
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (chartAt ℂ x).eventually_ne_nhdsWithin (mem_chart_source ℂ x)

omit [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- Pulling a chart expression back by the chart recovers the original function near its base
point. -/
private theorem chartExpression_comp_chartAt_eventuallyEq (x : X) (f : X → ℂ) :
    (fun y ↦ MeromorphicFunctionField.chartExpression X x f ((chartAt ℂ x) y)) =ᶠ[𝓝[≠] x] f := by
  -- On the chart source, the chart inverse cancels the chart itself.
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (chart_source_mem_nhds ℂ x)]
    with y hy
  simp [MeromorphicFunctionField.chartExpression, writtenInExtChartAt, (chartAt ℂ x).left_inv hy]

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Punctured neighborhoods on a connected complex manifold are nontrivial. -/
private theorem manifold_punctured_nhds_neBot (x : X) :
    Filter.NeBot (𝓝[≠] x) := by
  -- The complex chart supplies nontriviality, so the connected T1-space instance has no
  -- isolated points.
  -- Local instance justification (proof-local temporary data): the manifold's `T1Space`
  -- structure is needed only to derive nontriviality of this punctured neighborhood.
  letI : T1Space X := (𝓘(ℂ)).t1Space X
  -- Local instance justification (proof-local temporary data): the chosen point witnesses
  -- nontriviality only while constructing the punctured-neighborhood filter instance.
  letI : Nontrivial X := complexChartedSpace_nontrivial X x
  exact inferInstance

omit [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- A meromorphic representative is either eventually zero or eventually nonzero on each
punctured neighborhood. -/
private theorem isMeromorphic_eventually_eq_zero_or_eventually_ne_zero {f : X → ℂ}
    (hf : MeromorphicFunctionField.IsMeromorphic X f) (x : X) :
    f =ᶠ[𝓝[≠] x] 0 ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  -- Apply the one-variable meromorphic dichotomy in the chart coordinates.
  have hfx : MeromorphicAt (MeromorphicFunctionField.chartExpression X x f) ((chartAt ℂ x) x) := by
    simpa [MeromorphicFunctionField.IsMeromorphic, MeromorphicFunctionField.chartExpression] using hf x
  rcases hfx.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · left
    -- Transport the coordinate zero statement through the chart and rewrite to `f`.
    have hpull : ∀ᶠ y in 𝓝[≠] x, MeromorphicFunctionField.chartExpression X x f ((chartAt ℂ x) y) = 0 :=
      (chartAt_tendsto_punctured_nhds X x).eventually hzero
    have hrew := chartExpression_comp_chartAt_eventuallyEq X x f
    filter_upwards [hpull, hrew] with y hy hxy
    simpa [hxy.symm] using hy
  · right
    -- The nonzero branch is transported through the same chart bridge.
    have hpull : ∀ᶠ y in 𝓝[≠] x, MeromorphicFunctionField.chartExpression X x f ((chartAt ℂ x) y) ≠ 0 :=
      (chartAt_tendsto_punctured_nhds X x).eventually hnonzero
    have hrew := chartExpression_comp_chartAt_eventuallyEq X x f
    filter_upwards [hpull, hrew] with y hy hxy
    simpa [hxy.symm] using hy

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- If a function has a zero/nonzero punctured-neighborhood dichotomy at every point, then its
zero-germ locus is clopen. -/
private theorem eventuallyEqZeroSet_isClopen [T1Space X] (f : X → ℂ)
    (hdich : ∀ x : X, f =ᶠ[𝓝[≠] x] 0 ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0)
    (hne : ∀ x : X, Filter.NeBot (𝓝[≠] x)) :
    IsClopen {x | f =ᶠ[𝓝[≠] x] 0} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    -- At a point outside the zero-germ locus, the local dichotomy gives a nonzero punctured
    -- neighborhood, which excludes nearby zero germs by nontriviality of punctured filters.
    have hz_not : ¬ f =ᶠ[𝓝[≠] z] 0 := by simpa using hz
    rcases hdich z with hzero | hnonzero
    · exact False.elim (hz_not hzero)
    obtain ⟨t, ht_nonzero, ht_open, hz_mem⟩ :=
      eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hnonzero)
    refine ⟨t, ?_, ht_open, hz_mem⟩
    intro w hw hwS
    change ∀ᶠ y in 𝓝[≠] w, f y = (0 : X → ℂ) y at hwS
    by_cases hwz : w = z
    · apply hz_not
      change ∀ᶠ y in 𝓝[≠] z, f y = 0
      simpa [hwz] using hwS
    · have hnonzero_w : ∀ᶠ y in 𝓝[≠] w, f y ≠ 0 := by
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
        refine ⟨t \ {z}, ?_, ht_open.sdiff isClosed_singleton, ?_⟩
        · intro y hy _hyw
          exact ht_nonzero y hy.1 hy.2
        · exact ⟨hw, by simpa [Set.mem_singleton_iff] using hwz⟩
      have hcontra : ∀ᶠ y in 𝓝[≠] w, f y = (0 : X → ℂ) y ∧ f y ≠ 0 :=
        hwS.and hnonzero_w
      obtain ⟨y, hy⟩ := (hne w).nonempty_of_mem hcontra
      exact hy.2 (by simpa using hy.1)
  · rw [isOpen_iff_forall_mem_open]
    intro z hz
    -- A zero punctured neighborhood at `z` remains zero at every nearby point in the same
    -- neighborhood, after deleting `z`.
    obtain ⟨t, ht_zero, ht_open, hz_mem⟩ :=
      eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hz)
    refine ⟨t, ?_, ht_open, hz_mem⟩
    intro w hw
    change ∀ᶠ y in 𝓝[≠] w, f y = (0 : X → ℂ) y
    by_cases hwz : w = z
    · change ∀ᶠ y in 𝓝[≠] w, f y = 0
      change ∀ᶠ y in 𝓝[≠] z, f y = 0 at hz
      simpa [hwz] using hz
    · rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
      refine ⟨t \ {z}, ?_, ht_open.sdiff isClosed_singleton, ?_⟩
      · intro y hy _hyw
        exact ht_zero y hy.1 hy.2
      · exact ⟨hw, by simpa [Set.mem_singleton_iff] using hwz⟩

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- On a connected manifold, a meromorphic representative is either codiscretely zero or
codiscretely nonzero. -/
private theorem isMeromorphic_eq_zero_or_nonzero_mem_codiscrete {f : X → ℂ}
    (hf : MeromorphicFunctionField.IsMeromorphic X f) :
    f =ᶠ[Filter.codiscrete X] 0 ∨ {x | f x ≠ 0} ∈ Filter.codiscrete X := by
  -- The zero-germ locus is clopen, hence either empty or all of the connected space.
  -- Local instance justification (proof-local temporary data): the `T1Space` structure is
  -- used only to apply the local zero-germ clopenness criterion.
  letI : T1Space X := (𝓘(ℂ)).t1Space X
  have hclopen : IsClopen {x | f =ᶠ[𝓝[≠] x] 0} :=
    eventuallyEqZeroSet_isClopen X f
      (fun x ↦ isMeromorphic_eventually_eq_zero_or_eventually_ne_zero X hf x)
      (fun x ↦ manifold_punctured_nhds_neBot X x)
  rcases isClopen_iff.mp hclopen with hzeroSet | hzeroSet
  · right
    rw [mem_codiscrete]
    intro x
    rw [Filter.disjoint_principal_right]
    -- Empty zero-germ locus forces the nonzero branch at every point.
    have hx_not : ¬ f =ᶠ[𝓝[≠] x] 0 := by
      intro hx_zero
      have hx_mem : x ∈ ({x | f =ᶠ[𝓝[≠] x] 0} : Set X) := hx_zero
      rw [hzeroSet] at hx_mem
      exact hx_mem
    rcases isMeromorphic_eventually_eq_zero_or_eventually_ne_zero X hf x with hx_zero | hx_nonzero
    · exact False.elim (hx_not hx_zero)
    · simpa only [compl_compl] using
        (show {y : X | f y ≠ 0} ∈ 𝓝[≠] x from hx_nonzero)
  · left
    rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscrete]
    intro x
    rw [Filter.disjoint_principal_right]
    -- If every point has zero germ, those germs are exactly the codiscrete zero equality.
    have hx_mem : x ∈ ({x | f =ᶠ[𝓝[≠] x] 0} : Set X) := by
      rw [hzeroSet]
      exact Set.mem_univ x
    change ∀ᶠ y in 𝓝[≠] x, f y = (0 : X → ℂ) y at hx_mem
    simpa only [compl_compl] using
      (show {y : X | f y = (0 : X → ℂ) y} ∈ 𝓝[≠] x from hx_mem)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The codiscrete filter of a connected complex manifold is nontrivial. -/
private theorem codiscrete_neBot : Filter.NeBot (Filter.codiscrete X) := by
  rw [Filter.neBot_iff]
  intro hbot
  -- If the codiscrete filter were bottom, the empty set would be codiscrete.
  have hempty : (∅ : Set X) ∈ Filter.codiscrete X := by
    rw [Filter.empty_mem_iff_bot]
    exact hbot
  rw [mem_codiscrete] at hempty
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hxempty : (∅ : Set X) ∈ 𝓝[≠] x := by
    simpa using (Filter.disjoint_principal_right.mp (hempty x))
  exact @Filter.empty_notMem X (𝓝[≠] x) (manifold_punctured_nhds_neBot X x) hxempty

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem meromorphicFunctionField_zero_ne_one :
    (0 : ℂ(X)) ≠ 1 := by
  intro h
  -- Equality of quotient constants would make the contradictory constant equality hold on a
  -- codiscrete set.
  have hrel : ((0 : ↥(MeromorphicFunctionField.Representative.subalgebra X)) : X → ℂ) =ᶠ[Filter.codiscrete X]
      ((1 : ↥(MeromorphicFunctionField.Representative.subalgebra X)) : X → ℂ) := by
    have hrel' := (RingCon.eq (MeromorphicFunctionField.Representative.con X)).mp h
    simpa [MeromorphicFunctionField.Representative.con] using hrel'
  have hbad : ∀ᶠ (_ : X) in Filter.codiscrete X, (0 : ℂ) = 1 := hrel
  obtain ⟨x, hx⟩ := (codiscrete_neBot X).nonempty_of_mem hbad
  norm_num at hx

noncomputable instance : Nontrivial (ℂ(X)) :=
  ⟨0, 1, meromorphicFunctionField_zero_ne_one X⟩

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Every meromorphic class is either a unit or zero. -/
theorem MeromorphicFunctionField.isUnit_or_eq_zero (f : ℂ(X)) :
    IsUnit f ∨ f = 0 := by
  -- Work with a representative and use the global zero/nonzero dichotomy for that representative.
  refine Quotient.inductionOn f ?_
  intro a
  rcases isMeromorphic_eq_zero_or_nonzero_mem_codiscrete X a.property with hzero | hnonzero
  · right
    apply (RingCon.eq (MeromorphicFunctionField.Representative.con X)).mpr
    simpa [MeromorphicFunctionField.Representative.con] using hzero
  · left
    rw [isUnit_iff_exists_inv]
    refine ⟨(↑(a⁻¹) : RingCon.Quotient (MeromorphicFunctionField.Representative.con X)), ?_⟩
    apply (RingCon.eq (MeromorphicFunctionField.Representative.con X)).mpr
    rw [MeromorphicFunctionField.Representative.con]
    -- On the codiscrete nonzero set, the pointwise inverse is a multiplicative inverse.
    filter_upwards [hnonzero] with x hx
    simpa [representative_inv_apply] using mul_inv_cancel₀ hx

/-- The meromorphic function field `ℂ(X)` of a connected complex one-manifold carries its
canonical field structure. -/
noncomputable instance : Field (MeromorphicFunctionField X) :=
  Field.ofIsUnitOrEqZero fun f ↦ MeromorphicFunctionField.isUnit_or_eq_zero X f

/-- Taking quotient classes commutes with pointwise inversion of representatives. -/
@[simp]
theorem MeromorphicFunctionField.mk_inv {f : X → ℂ}
    (hf : MeromorphicFunctionField.IsMeromorphic X f) :
    MeromorphicFunctionField.mk X f⁻¹
      (MeromorphicFunctionField.IsMeromorphic.inv X hf) =
      (MeromorphicFunctionField.mk X f hf)⁻¹ := by
  rcases isMeromorphic_eq_zero_or_nonzero_mem_codiscrete X hf with hzero | hnonzero
  · rw [MeromorphicFunctionField.mk_eq_zero_of_eventuallyEq_zero X hzero, inv_zero]
    apply MeromorphicFunctionField.mk_eq_zero_of_eventuallyEq_zero X
    filter_upwards [hzero] with x hx
    change f x = 0 at hx
    change (f x)⁻¹ = 0
    rw [hx, inv_zero]
  · symm
    apply inv_eq_of_mul_eq_one_right
    rw [← MeromorphicFunctionField.mk_mul X hf (MeromorphicFunctionField.IsMeromorphic.inv X hf),
      ← MeromorphicFunctionField.mk_one X]
    apply MeromorphicFunctionField.mk_eq_mk_of_eventuallyEq X
    filter_upwards [hnonzero] with x hx
    exact mul_inv_cancel₀ hx

end
