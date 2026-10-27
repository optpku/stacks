/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.Family
public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.SubcomplexSupply
public import Mathlib.Tactic.CrossRefAttribute

/-! # The transfinite acyclic reduction tower of Stacks 079L

Let `M` be an acyclic cochain complex in a Grothendieck abelian category. The proof of
Stacks 079L builds, by transfinite induction on ordinals, acyclic subcomplexes
`K_α ⊆ M`:

* `K_0 = 0`;
* for `α = β + 1`, if `K_β = M` then `K_α = K_β`; otherwise `M / K_β` is a nonzero acyclic
  complex, one chooses a small bounded-above acyclic subcomplex `N_α ⊆ M / K_β` as in
  Stacks 079K, and `K_α` is its inverse image in `M`;
* for a limit ordinal `α`, `K_α` is the colimit (union) of the `K_β`, `β < α`.

`SmallAcyclic.SubcomplexSupply` is the data-level form of Stacks 079K (1): an actual
assignment of a nonzero small acyclic subcomplex to every nonzero acyclic complex.
`AcyclicReduction` packages an ordinal-indexed monotone tower of actual subobjects of `M`
with the source's successor short exact sequences `0 → K_β → K_{β+1} → N_{β+1} → 0`, the
native colimit cocones at limit ordinals, and an exhaustion stage. `AcyclicReduction.ofSupply`
constructs it from a supply by the native `transfiniteIterate` recursion on `Subobject M`:
successor stages are the native `Subobject.pullback` along the cokernel projection, limit
stages are suprema, and the limit `IsColimit` is mathlib's
`IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`. No subcomplex is selected
from an existence statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe z w v u

namespace CochainComplex

namespace AcyclicReduction

variable {C : Type u} [Category.{v} C] [Abelian C] {M : CochainComplex C ℤ}

/-- Restriction of an ordinal-indexed monotone tower of subobjects to the ordinals below `α`,
as a diagram of monomorphisms over `M` indexed by the small well-order `α.ToType`. -/
def limitDiagram (stage : Ordinal.{w} → Subobject M) (hstage : Monotone stage)
    (α : Ordinal.{w}) : α.ToType ⥤ MonoOver M :=
  (show Monotone fun j : α.ToType ↦ stage (j : Ordinal) from
    fun _ _ hij ↦ hstage (Ordinal.ToType.mk.symm.monotone hij)).functor ⋙
      Subobject.representative

/-- The inclusions `K_β ⟶ K_α`, `β < α`, as a cocone over `M`. -/
def limitOverCocone (stage : Ordinal.{w} → Subobject M) (hstage : Monotone stage)
    (α : Ordinal.{w}) : Cocone (limitDiagram stage hstage α ⋙ MonoOver.forget M) where
  pt := Over.mk (stage α).arrow
  ι :=
    { app j := Over.homMk (Subobject.ofLE (stage (j : Ordinal)) (stage α)
          (hstage (j.toOrd.2.le))) (Subobject.ofLE_arrow _)
      naturality _ _ _ :=
        Over.OverMorphism.ext ((cancel_mono (stage α).arrow).1
          ((Over.w _).trans (Over.w _).symm)) }

/-- The diagram of the stages below `α` in the category of complexes. -/
abbrev limitFunctor (stage : Ordinal.{w} → Subobject M) (hstage : Monotone stage)
    (α : Ordinal.{w}) : α.ToType ⥤ CochainComplex C ℤ :=
  (limitDiagram stage hstage α ⋙ MonoOver.forget M) ⋙ Over.forget M

/-- The cocone of inclusions `K_β ⟶ K_α`, `β < α`, in the category of complexes. -/
def limitCocone (stage : Ordinal.{w} → Subobject M) (hstage : Monotone stage)
    (α : Ordinal.{w}) : Cocone (limitFunctor stage hstage α) :=
  (Over.forget M).mapCocone (limitOverCocone stage hstage α)

/-- The vertex of the ordinal-stage cocone is the corresponding subcomplex. -/
@[simp]
lemma limitCocone_pt (stage : Ordinal.{w} → Subobject M) (hstage : Monotone stage)
    (α : Ordinal.{w}) : (limitCocone stage hstage α).pt = (stage α : CochainComplex C ℤ) :=
  rfl

/-- The cocone legs are the canonical inclusions between ordinal stages. -/
@[simp]
lemma limitCocone_ι_app (stage : Ordinal.{w} → Subobject M) (hstage : Monotone stage)
    (α : Ordinal.{w}) (j : α.ToType) :
    (limitCocone stage hstage α).ι.app j =
      Subobject.ofLE (stage (j : Ordinal)) (stage α) (hstage (j.toOrd.2.le)) :=
  rfl

end AcyclicReduction

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- An ordinal-indexed tower of acyclic subcomplexes `K_α ⊆ M` with
`K_0 = 0`, successor short exact sequences `0 → K_β → K_{β+1} → N_{β+1} → 0` whose quotients are
small bounded-above acyclic complexes while `K_β ≠ M` (and `K_{β+1} = K_β` once `K_β = M`),
limit stages the colimits of the earlier stages, and an actual stage equal to `M`. -/
@[stacks 079L "transfinite acyclic reduction tower"]
structure AcyclicReduction (M : CochainComplex C ℤ) (kappa : Cardinal.{z}) where
  /-- The subcomplex `K_α ⊆ M`. -/
  stage : Ordinal.{w} → Subobject M
  /-- The stages increase with the ordinal. -/
  monotone : Monotone stage
  /-- `K_0 = 0`. -/
  stage_zero : stage 0 = ⊥
  /-- Every stage is an acyclic complex. -/
  acyclic (α : Ordinal.{w}) : (stage α : CochainComplex C ℤ).Acyclic
  /-- The successor quotient `N_{β+1} = K_{β+1} / K_β`. -/
  quotient : Ordinal.{w} → CochainComplex C ℤ
  /-- The projection `K_{β+1} ⟶ N_{β+1}`. -/
  π (β : Ordinal.{w}) : (stage (Order.succ β) : CochainComplex C ℤ) ⟶ quotient β
  /-- The inclusion `K_β ⟶ K_{β+1}` followed by the projection is zero. -/
  inclusion_π (β : Ordinal.{w}) :
    Subobject.ofLE (stage β) (stage (Order.succ β)) (monotone (Order.le_succ β)) ≫ π β = 0
  /-- The successor sequence `0 → K_β → K_{β+1} → N_{β+1} → 0` is short exact. -/
  shortExact (β : Ordinal.{w}) :
    (ShortComplex.mk _ _ (inclusion_π β)).ShortExact
  /-- While `K_β ≠ M`, the quotient `N_{β+1}` is a small bounded-above
  acyclic complex. -/
  quotient_boundedBy (β : Ordinal.{w}) (h : stage β ≠ ⊤) : SmallAcyclic.BoundedBy kappa (quotient β)
  /-- While `K_β ≠ M`, the quotient `N_{β+1}` is nonzero. -/
  quotient_not_isZero (β : Ordinal.{w}) (h : stage β ≠ ⊤) : ¬ IsZero (quotient β)
  /-- Once `K_β = M`, the next stage is unchanged. -/
  stage_succ_of_eq_top (β : Ordinal.{w}) (h : stage β = ⊤) : stage (Order.succ β) = stage β
  /-- A limit stage is the union of the earlier stages. -/
  stage_limit (α : Ordinal.{w}) (hα : Order.IsSuccLimit α) :
    stage α = ⨆ β : Set.Iio α, stage β.1
  /-- A limit stage is the colimit of the earlier stages, via the inclusions. -/
  isColimit (α : Ordinal.{w}) (hα : Order.IsSuccLimit α) :
    IsColimit (AcyclicReduction.limitCocone stage monotone α)
  /-- An ordinal at which the tower exhausts `M`. -/
  exhaustion : Ordinal.{w}
  /-- `K_α = M` at the exhaustion stage. -/
  stage_exhaustion : stage exhaustion = ⊤

namespace AcyclicReduction

variable {M : CochainComplex C ℤ} {kappa : Cardinal.{z}}

/-- The successor short complex `0 → K_β → K_{β+1} → N_{β+1} → 0`. -/
abbrev successor (R : AcyclicReduction M kappa) (β : Ordinal.{w}) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk _ _ (R.inclusion_π β)

/-- Every stage after the exhaustion stage is all of `M`. -/
theorem stage_eq_top_of_le (R : AcyclicReduction M kappa) {α : Ordinal.{w}}
    (hα : R.exhaustion ≤ α) : R.stage α = ⊤ :=
  top_le_iff.mp (R.stage_exhaustion ▸ R.monotone hα)

/-- The exhaustion stage is isomorphic to the ambient complex, with both maps given by
native subobject inclusions and the representative isomorphism of the top subobject. -/
def exhaustionIso (R : AcyclicReduction M kappa) :
    (R.stage R.exhaustion : CochainComplex C ℤ) ≅ M :=
  Subobject.isoOfEq _ _ R.stage_exhaustion ≪≫ Subobject.underlyingIso (𝟙 M)

/-- The exhaustion isomorphism has the native subobject inclusion as its forward map. -/
@[simp]
lemma exhaustionIso_hom (R : AcyclicReduction M kappa) :
    R.exhaustionIso.hom = (R.stage R.exhaustion).arrow := by
  simp [exhaustionIso, Subobject.underlyingIso_top_hom]

/-- `M` is acyclic, being an exhaustion stage of the tower. -/
theorem acyclic_ambient (R : AcyclicReduction M kappa) : M.Acyclic :=
  (R.acyclic R.exhaustion).of_iso R.exhaustionIso

/-- The inclusion of the exhaustion stage is an isomorphism onto `M`. -/
theorem isIso_arrow_exhaustion (R : AcyclicReduction M kappa) :
    IsIso (R.stage R.exhaustion).arrow :=
  (Subobject.isIso_arrow_iff_eq_top _).mpr R.stage_exhaustion

end AcyclicReduction

namespace AcyclicReduction

variable {M : CochainComplex C ℤ}

/-- The specified nonzero small acyclic subcomplex of `M / K` when `M / K` is nonzero and
acyclic (the source's case `K ≠ M`), and the zero subcomplex otherwise. The cokernel is the
native one of `K ⟶ M`. -/
def quotientSub {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (K : Subobject M) : Subobject (cokernel K.arrow) :=
  open Classical in
  if h : ¬ IsZero (cokernel K.arrow) ∧ (cokernel K.arrow).Acyclic then
    S.sub (cokernel K.arrow) h.2 h.1
  else ⊥

/-- The successor step: the inverse image in `M` of the specified subcomplex of `M / K`. -/
def step {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (K : Subobject M) : Subobject M :=
  (Subobject.pullback (cokernel.π K.arrow)).obj (quotientSub S K)

/-- The inverse image of a subcomplex of `M / K` contains `K`. -/
theorem le_step {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (K : Subobject M) : K ≤ step S K := by
  change K ≤ (Subobject.pullback (cokernel.π K.arrow)).obj (quotientSub S K)
  exact Subobject.le_of_comm
    ((Subobject.isPullback (cokernel.π K.arrow) (quotientSub S K)).lift 0 K.arrow (by simp))
    (by simp)

/-- The tower `K_α`: transfinite iteration of `step` from `K_0 = 0`, with suprema at limit
ordinals. -/
def stageOf {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (α : Ordinal.{w}) : Subobject M :=
  transfiniteIterate (step S) α ⊥

/-- The transfinite stage construction is monotone in its ordinal index. -/
theorem stageOf_monotone {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa) :
    Monotone (stageOf (M := M) S : Ordinal.{w} → Subobject M) :=
  monotone_transfiniteIterate _ _ (le_step S)

/-- The initial stage of the transfinite construction is the bottom subobject. -/
theorem stageOf_zero {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa) :
    stageOf (M := M) S (0 : Ordinal.{w}) = ⊥ := by
  rw [← Ordinal.bot_eq_zero]
  exact transfiniteIterate_bot _ _

/-- `K_{β+1}` is the inverse image of the specified subcomplex of `M / K_β`. -/
theorem stageOf_succ {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (β : Ordinal.{w}) :
    (stageOf (M := M) S (Order.succ β : Ordinal.{w})) = step S (stageOf S β) :=
  transfiniteIterate_succ _ _ _ (not_isMax β)

/-- A limit stage is the supremum of the earlier stages. -/
theorem stageOf_limit {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (α : Ordinal.{w}) (hα : Order.IsSuccLimit α) :
    stageOf (M := M) S α = ⨆ β : Set.Iio α, stageOf S β.1 :=
  transfiniteIterate_limit _ _ _ hα

/-- The successor quotient `N_{β+1}`: the specified subcomplex of `M / K_β`. -/
def quotientOf {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (β : Ordinal.{w}) : CochainComplex C ℤ :=
  (quotientSub S (stageOf (M := M) S β) : CochainComplex C ℤ)

/-- The projection `K_{β+1} ⟶ N_{β+1}`: the native pullback projection of the inverse image. -/
def πOf {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (β : Ordinal.{w}) :
    ((stageOf (M := M) S (Order.succ β : Ordinal.{w})) : CochainComplex C ℤ) ⟶ quotientOf (M := M) S β :=
  (Subobject.isoOfEq _ _ (stageOf_succ S β)).hom ≫
    Subobject.pullbackπ (cokernel.π (stageOf (M := M) S β).arrow)
      (quotientSub S (stageOf S β))

/-- The limit cocone of the constructed tower is a colimit: native Grothendieck AB5 for
directed unions of subobjects. -/
def isColimitOf {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (α : Ordinal.{w}) (hα : Order.IsSuccLimit α) :
    IsColimit (limitCocone (stageOf (M := M) S) (stageOf_monotone S) α) := by
  -- Local instance justification (proof-local temporary data): a nonzero limit ordinal
  -- has a nonempty type of predecessors, so its linear order is filtered.
  haveI : Nonempty α.ToType := Ordinal.nonempty_toType_iff.mpr (Ordinal.bot_eq_zero ▸ hα.ne_bot)
  -- Local instance justification (defeq pin): expose the canonical mono of the stage
  -- as the mono of the cocone vertex's structure morphism.
  haveI : Mono (limitOverCocone (stageOf (M := M) S) (stageOf_monotone S) α).pt.hom :=
    inferInstanceAs (Mono (stageOf S α).arrow)
  exact IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
    (limitDiagram (stageOf S) (stageOf_monotone S) α)
    (limitOverCocone (stageOf S) (stageOf_monotone S) α) (by
      change Subobject.mk (stageOf (M := M) S α).arrow =
        ⨆ j : α.ToType, Subobject.mk (stageOf (M := M) S (j : Ordinal)).arrow
      simp only [Subobject.mk_arrow]
      rw [stageOf_limit S α hα, ← Ordinal.ToType.mk.toEquiv.iSup_comp]
      simp)

/-- The exhaustion stage: the least ordinal at which the tower reaches `M`. -/
def exhaustionOf {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa) :
    Ordinal.{w} :=
  sInf {α : Ordinal.{w} | stageOf (M := M) S α = ⊤}

private lemma step_zero {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (K : Subobject M) :
    Subobject.ofLE K (step S K) (le_step S K) ≫
      Subobject.pullbackπ (cokernel.π K.arrow) (quotientSub S K) = 0 := by
  apply (cancel_mono (quotientSub S K).arrow).mp
  rw [Category.assoc, (Subobject.isPullback
    (cokernel.π K.arrow) (quotientSub S K)).w, ← Category.assoc]
  change (Subobject.ofLE K (step S K) (le_step S K) ≫
    (step S K).arrow) ≫ cokernel.π K.arrow = _
  simp only [Subobject.ofLE_arrow, cokernel.condition, zero_comp]

private lemma step_shortExact {kappa : Cardinal.{z}}
    (S : SmallAcyclic.SubcomplexSupply C kappa) (K : Subobject M) :
    (ShortComplex.mk _ _ (step_zero S K)).ShortExact := by
  let sq := Subobject.isPullback (cokernel.π K.arrow) (quotientSub S K)
  have hker := KernelFork.IsLimit.ofι'
    (Subobject.ofLE K (step S K) (le_step S K)) (step_zero S K)
    (fun {A} a ha ↦ by
      have hz : (a ≫ (step S K).arrow) ≫ cokernel.π K.arrow = 0 := by
        dsimp only [step]
        rw [Category.assoc, ← sq.w, ← Category.assoc, ha, zero_comp]
      refine ⟨Abelian.monoLift K.arrow (a ≫ (step S K).arrow) hz, ?_⟩
      apply (cancel_mono (step S K).arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow, Abelian.monoLift_comp])
  have hepi : Epi (Subobject.pullbackπ (cokernel.π K.arrow) (quotientSub S K)) := by
    rw [← sq.isoPullback_hom_fst]
    infer_instance
  exact ⟨(ShortComplex.mk _ _ (step_zero S K)).exact_of_f_is_kernel hker⟩

private lemma acyclic_of_isColimit {D : Type w} [Category.{w} D]
    [HasExactColimitsOfShape D C] (F : D ⥤ CochainComplex C ℤ)
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ j, (F.obj j).Acyclic) :
    c.pt.Acyclic := by
  intro i
  let E := (ShortComplex.functorEquivalence D C).inverse.obj
    (F ⋙ HomologicalComplex.shortComplexFunctor C (.up ℤ) i)
  have hE : E.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    ext j
    exact (IsZero.of_iso ((hF j i).isZero_homology)
      (E.mapHomologyIso ((evaluation D C).obj j)).symm).eq_of_src _ _
  exact colim.exact_mapShortComplex hE
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) ((ComplexShape.up ℤ).prev i)) hc)
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hc)
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) ((ComplexShape.up ℤ).next i)) hc)
    (c.pt.d _ _) (c.pt.d _ _) (fun j ↦ (c.ι.app j).comm _ _)
    (fun j ↦ (c.ι.app j).comm _ _)

private lemma quotientSub_acyclic {kappa : Cardinal.{z}}
    (S : SmallAcyclic.SubcomplexSupply C kappa) (K : Subobject M) :
    (quotientSub S K : CochainComplex C ℤ).Acyclic := by
  classical
  dsimp only [quotientSub]
  split
  · exact (S.boundedBy _ _ _).acyclic
  · exact HomologicalComplex.acyclic_of_isZero _
      ((isZero_zero _).of_iso Subobject.botCoeIsoZero)

private lemma stageOf_acyclic {kappa : Cardinal.{z}}
    (S : SmallAcyclic.SubcomplexSupply C kappa) (α : Ordinal.{w}) :
    (stageOf (M := M) S α : CochainComplex C ℤ).Acyclic := by
  induction α using SuccOrder.limitRecOn with
  | isMin α hα =>
    have hzero : α = 0 := hα.eq_bot
    rw [hzero, stageOf_zero]
    exact HomologicalComplex.acyclic_of_isZero _
      ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
  | succ α hα ih =>
    rw [stageOf_succ]
    exact (step_shortExact S (stageOf S α)).acyclic_X₂ ih (quotientSub_acyclic S _)
  | isSuccLimit α hα ih =>
    -- Local instance justification (proof-local temporary data): The nonzero limit ordinal has a nonempty predecessor category, as required for this filtered colimit.
    haveI : Nonempty α.ToType := Ordinal.nonempty_toType_iff.mpr
      (Ordinal.bot_eq_zero ▸ hα.ne_bot)
    exact acyclic_of_isColimit _ _ (isColimitOf S α hα) (fun j ↦ ih j j.toOrd.2)

private lemma cokernel_acyclic (K : Subobject M) (hM : M.Acyclic)
    (hK : (K : CochainComplex C ℤ).Acyclic) : (cokernel K.arrow).Acyclic := by
  have hq : QuasiIso K.arrow := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt K.arrow i (hK i)).mpr (hM i)
  exact (show (ShortComplex.mk _ _ (cokernel.condition K.arrow)).ShortExact from
    ⟨ShortComplex.exact_cokernel K.arrow⟩).acyclic_X₃ hq

private lemma cokernel_not_isZero (K : Subobject M) (hK : K ≠ ⊤) :
    ¬ IsZero (cokernel K.arrow) := by
  intro hz
  -- Local instance justification (proof-local temporary data): The assumed zero cokernel makes this particular subobject inclusion epic for the abelian mono-epi criterion.
  haveI : Epi K.arrow := Abelian.epi_of_cokernel_π_eq_zero _ (hz.eq_of_tgt _ _)
  exact hK ((Subobject.isIso_arrow_iff_eq_top K).mp (isIso_of_mono_of_epi K.arrow))

private lemma stageOf_lt_succ {kappa : Cardinal.{z}}
    (S : SmallAcyclic.SubcomplexSupply C kappa) (hM : M.Acyclic) (α : Ordinal.{w})
    (hne : stageOf (M := M) S α ≠ ⊤) :
    stageOf (M := M) S α < stageOf (M := M) S (Order.succ α) := by
  refine lt_of_le_of_ne (stageOf_monotone S (Order.le_succ α)) ?_
  intro heq
  let K := stageOf (M := M) S α
  have hK : K = step S K := heq.trans (stageOf_succ S α)
  -- Local instance justification (proof-local temporary data): The assumed equality of these stages makes this particular inclusion invertible for cancellation.
  haveI : IsIso (Subobject.ofLE K (step S K) (le_step S K)) := by
    rw [← Subobject.isoOfEq_hom K (step S K) hK]
    infer_instance
  have hz : Subobject.pullbackπ (cokernel.π K.arrow) (quotientSub S K) = 0 := by
    apply (cancel_epi (Subobject.ofLE K (step S K) (le_step S K))).mp
    simpa only [comp_zero] using step_zero S K
  -- Local instance justification (proof-local temporary data): The short-exact successor projection is epic, so its vanishing implies that its quotient target is a zero object.
  haveI : Epi (Subobject.pullbackπ (cokernel.π K.arrow) (quotientSub S K)) :=
    (step_shortExact S K).epi_g
  have hnonzero : ¬ IsZero (quotientSub S K : CochainComplex C ℤ) := by
    have h := And.intro (cokernel_not_isZero K hne)
      (cokernel_acyclic K hM (stageOf_acyclic S α))
    dsimp only [quotientSub]
    rw [dif_pos h]
    exact S.not_isZero _ _ _
  exact hnonzero (IsZero.of_epi_eq_zero _ hz)

private lemma stageOf_exhaustion {kappa : Cardinal.{z}}
    (S : SmallAcyclic.SubcomplexSupply C kappa) (hM : M.Acyclic) :
    stageOf (M := M) S (exhaustionOf (M := M) S) = ⊤ := by
  change sInf {α : Ordinal.{w} | stageOf (M := M) S α = ⊤} ∈
    {α : Ordinal.{w} | stageOf (M := M) S α = ⊤}
  apply csInf_mem
  by_contra h
  have hn (α : Ordinal.{w}) : stageOf (M := M) S α ≠ ⊤ :=
    fun hα ↦ h ⟨α, hα⟩
  have hstrict : StrictMono (stageOf (M := M) S : Ordinal.{w} → Subobject M) := by
    intro α β hαβ
    exact (stageOf_lt_succ S hM α (hn α)).trans_le
      (stageOf_monotone S (Order.succ_le_of_lt hαβ))
  exact not_injective_of_ordinal _ hstrict.injective

/-- The transfinite acyclic reduction tower of an acyclic complex,
constructed from a data-level supply of small acyclic subcomplexes. -/
@[stacks 079L "construction of the acyclic reduction tower"]
def ofSupply {kappa : Cardinal.{z}} (S : SmallAcyclic.SubcomplexSupply C kappa)
    (hM : M.Acyclic) : AcyclicReduction M kappa where
  stage := stageOf S
  monotone := stageOf_monotone S
  stage_zero := stageOf_zero S
  acyclic α := by exact stageOf_acyclic S α
  quotient := quotientOf S
  π := πOf S
  inclusion_π β := by
    apply (cancel_mono (quotientSub S (stageOf S β)).arrow).mp
    dsimp only [πOf]
    simp only [Category.assoc, step, (Subobject.isPullback
      (cokernel.π (stageOf S β).arrow) (quotientSub S (stageOf S β))).w,
      Subobject.isoOfEq_hom, Subobject.ofLE_arrow_assoc,
      Subobject.ofLE_arrow, cokernel.condition, zero_comp]
  shortExact β := by
    refine ShortComplex.shortExact_of_iso ?_
      (step_shortExact S (stageOf (M := M) S β))
    refine ShortComplex.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ (stageOf_succ S β)).symm (Iso.refl _) ?_ ?_
    · apply (cancel_mono (stageOf S (Order.succ β)).arrow).mp
      simp only [Iso.refl_hom, Category.id_comp, Category.assoc, Iso.symm_hom,
        Subobject.isoOfEq_inv, Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, πOf, Iso.symm_hom,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  quotient_boundedBy β hβ := by
    have h := And.intro (cokernel_not_isZero (stageOf S β) hβ)
      (cokernel_acyclic (stageOf S β) hM (stageOf_acyclic S β))
    dsimp only [quotientOf, quotientSub]
    rw [dif_pos h]
    exact S.boundedBy _ _ _
  quotient_not_isZero β hβ := by
    have h := And.intro (cokernel_not_isZero (stageOf S β) hβ)
      (cokernel_acyclic (stageOf S β) hM (stageOf_acyclic S β))
    dsimp only [quotientOf, quotientSub]
    rw [dif_pos h]
    exact S.not_isZero _ _ _
  stage_succ_of_eq_top β hβ := by
    rw [stageOf_succ, hβ]
    exact top_unique (le_step S ⊤)
  stage_limit := stageOf_limit S
  isColimit := isColimitOf S
  exhaustion := exhaustionOf (M := M) S
  stage_exhaustion := by exact stageOf_exhaustion S hM

end AcyclicReduction

end CochainComplex
