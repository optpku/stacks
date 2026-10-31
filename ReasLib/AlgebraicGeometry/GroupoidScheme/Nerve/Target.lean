/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicTopology.Cech.Nerve.LowDegree
public import ReasLib.AlgebraicGeometry.SimplicialScheme.CechNerve
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Nerve

/-!
# Target simplicial morphism of a groupoid scheme

A groupoid scheme `G` over `S` determines a morphism `t_•` from the Čech nerve of `s` to the
associated simplicial scheme, sending `(r₀, …, rₙ)` to `(r₀ ∘ r₁⁻¹, …, rₙ₋₁ ∘ rₙ⁻¹)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The first arrow and the inverse of the second arrow of a common-source pair are composable. -/
private theorem rightDivisionCondition :
    pullback.fst G.s G.s ≫ G.s = (pullback.snd G.s G.s ≫ G.i) ≫ G.t := by
  simpa only [Category.assoc, G.inverse_target] using (pullback.condition (f := G.s) (g := G.s))

/-- For two arrows with a common source, compose the first with the inverse of the second. -/
def rightDivision : pullback G.s G.s ⟶ G.R :=
  G.compose (pullback.fst G.s G.s) (pullback.snd G.s G.s ≫ G.i) (by exact rightDivisionCondition G)

/-- The source of a right quotient is the target of the second arrow. -/
theorem rightDivision_source : G.rightDivision ≫ G.s = pullback.snd G.s G.s ≫ G.t := by
  simp [rightDivision, compose, Category.assoc, G.comp_source, pullback.lift_snd_assoc,
    G.inverse_source]

/-- The target of a right quotient is the target of the first arrow. -/
theorem rightDivision_target : G.rightDivision ≫ G.t = pullback.fst G.s G.s ≫ G.t := by
  simp [rightDivision, compose, Category.assoc, G.comp_target, pullback.lift_fst_assoc]

/-- Degree `n` of the Čech nerve of `s`, as a scheme over `S` via the base projection through `U`. -/
def sourceCechOver (n : SimplexCategoryᵒᵖ) : Over S :=
  Over.mk (Arrow.cechNerve.base (Arrow.mk G.s.left) n ≫ G.U.hom)

/-- The structure morphism of `sourceCechOver` is the Čech-nerve base projection followed by `U ⟶ S`. -/
theorem sourceCechOver_hom (n : SimplexCategoryᵒᵖ) :
    (sourceCechOver G n).hom = Arrow.cechNerve.base (Arrow.mk G.s.left) n ≫ G.U.hom :=
  rfl

/-- Each Čech-nerve vertex projection of `s` is a morphism over `S`. -/
private theorem sourceCechπOver_w (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    Arrow.cechNerve.π (Arrow.mk G.s.left) n i ≫ G.R.hom = (sourceCechOver G n).hom := by
  have h : Arrow.cechNerve.π (Arrow.mk G.s.left) n i ≫ G.s.left =
      Arrow.cechNerve.base (Arrow.mk G.s.left) n := by
    apply WidePullback.π_arrow
  calc
    _ = Arrow.cechNerve.π (Arrow.mk G.s.left) n i ≫ (G.s.left ≫ G.U.hom) :=
      congrArg (fun f => Arrow.cechNerve.π (Arrow.mk G.s.left) n i ≫ f) (Over.w G.s).symm
    _ = (Arrow.cechNerve.π (Arrow.mk G.s.left) n i ≫ G.s.left) ≫ G.U.hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ G.U.hom) h

/-- The vertex projection `π i : (R/U)_n ⟶ R` as a morphism of schemes over `S`. -/
def sourceCechπOver (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    sourceCechOver G n ⟶ G.R :=
  Over.homMk (Arrow.cechNerve.π (Arrow.mk G.s.left) n i) (by exact sourceCechπOver_w G n i)

/-- The underlying scheme morphism of `sourceCechπOver` is the Čech-nerve vertex projection. -/
theorem sourceCechπOver_left (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    (sourceCechπOver G n i).left = Arrow.cechNerve.π (Arrow.mk G.s.left) n i :=
  rfl

/-- Consecutive Čech projections become composable after inverting the later one. -/
private theorem sourceCechRightDivisionCondition (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechπOver G n i.castSucc ≫ G.s =
      (sourceCechπOver G n i.succ ≫ G.i) ≫ G.t := by
  rw [Category.assoc, G.inverse_target]
  apply Over.OverMorphism.ext
  exact (WidePullback.π_arrow (fun _ => G.s.left) i.castSucc).trans
    (WidePullback.π_arrow (fun _ => G.s.left) i.succ).symm

/-- The source formula component `rᵢ ∘ rᵢ₊₁⁻¹` on a Čech degree. -/
def sourceCechRightDivision (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechOver G n ⟶ G.R :=
  G.compose (sourceCechπOver G n i.castSucc) (sourceCechπOver G n i.succ ≫ G.i)
    (by exact sourceCechRightDivisionCondition G n i)

/-- The source of `rᵢ ∘ rᵢ₊₁⁻¹` is the target of `rᵢ₊₁`. -/
theorem sourceCechRightDivision_source (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechRightDivision G n i ≫ G.s = sourceCechπOver G n i.succ ≫ G.t := by
  simp [sourceCechRightDivision, compose, Category.assoc, G.comp_source,
    pullback.lift_snd_assoc, G.inverse_source]

/-- The target of `rᵢ ∘ rᵢ₊₁⁻¹` is the target of `rᵢ`. -/
theorem sourceCechRightDivision_target (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechRightDivision G n i ≫ G.t = sourceCechπOver G n i.castSucc ≫ G.t := by
  simp [sourceCechRightDivision, compose, Category.assoc, G.comp_target, pullback.lift_fst_assoc]

/-- The degree-`n` map from the source Čech nerve to the product of composable arrows,
formed from the adjacent right quotients with vertices numbered from source to target. -/
def targetOver (n : ℕ) : sourceCechOver G (op ⦋n⦌) ⟶ composable G n :=
  G.ofComposableArrows n
    (ComposableArrows.mkOfObjOfMapSucc
      (C := G.groupoidPoints (sourceCechOver G (op ⦋n⦌)))
      (fun i => sourceCechπOver G (op ⦋n⦌) i.rev ≫ G.t)
      (fun i => PointHom.ofArrow (sourceCechRightDivision G (op ⦋n⦌) i.rev)
        (by
          simpa only [Fin.rev_castSucc] using
            sourceCechRightDivision_source G (op ⦋n⦌) i.rev)
        (by
          simpa only [Fin.rev_succ] using
            sourceCechRightDivision_target G (op ⦋n⦌) i.rev)))

/-- In degree `0`, `targetOver` is the target map after the unique Čech projection. -/
theorem targetOver_zero : targetOver G 0 = sourceCechπOver G (op ⦋0⦌) 0 ≫ G.t := by
  rfl

/-- In degree `1`, `targetOver` is right division of the two Čech projections. -/
theorem targetOver_one : targetOver G 1 = sourceCechRightDivision G (op ⦋1⦌) 0 := by
  unfold targetOver
  simp only [ofComposableArrows, ComposableArrows.mkOfObjOfMapSucc_map_succ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Reconstruction preserves each reverse-indexed adjacent arrow of a pointwise simplex. -/
private theorem ofComposableArrows_π {T : Over S} (n : ℕ)
    (F : ComposableArrows (G.groupoidPoints T) (n + 1))
    (i : Fin (n + 1)) :
    ofComposableArrows G (n + 1) F ≫ composableπ G (n + 1) i =
      (F.map (homOfLE (Fin.castSucc_le_succ i.rev))).arrow := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change (F.map' 0 1).arrow ≫ 𝟙 G.R = (F.map' 0 1).arrow
      exact Category.comp_id _
  | succ n ih =>
      have hc : (F.map' (n + 1) (n + 2)).arrow ≫ G.s =
          ofComposableArrows G (n + 1) F.δlast ≫
            ((composableWithπ G (n + 1)).2 0 ≫ G.t) := by
        change (F.map' (n + 1) (n + 2)).arrow ≫ G.s =
          ofComposableArrows G (n + 1) F.δlast ≫ (composableπ G (n + 1) 0 ≫ G.t)
        rw [← Category.assoc, ih F.δlast 0]
        exact (F.map' (n + 1) (n + 2)).source.trans
          (F.δlast.map (homOfLE (Fin.castSucc_le_succ (0 : Fin (n + 1)).rev))).target.symm
      have hrec : ofComposableArrows G (n + 2) F =
          pullback.lift (F.map' (n + 1) (n + 2)).arrow
            (ofComposableArrows G (n + 1) F.δlast) hc := rfl
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hrec, composableπ, composableWithπ]
      · change (pullback.lift _ (ofComposableArrows G (n + 1) F.δlast) hc ≫
          (pullback.snd _ _ ≫ composableπ G (n + 1) j)) = _
        rw [← Category.assoc, pullback.lift_snd]
        let d : Fin (n + 2) → (T ⟶ G.R) :=
          fun k => (F.map (homOfLE (Fin.castSucc_le_succ k))).arrow
        have hd : (F.δlast.map (homOfLE (Fin.castSucc_le_succ j.rev))).arrow =
            d j.rev.castSucc := rfl
        exact (ih F.δlast j).trans (hd.trans (congrArg d (Fin.rev_succ j).symm))

set_option backward.isDefEq.respectTransparency false in
/-- The later-first projections of `targetOver` are the consecutive right divisions of Čech
projections. -/
theorem targetSimplicial_π (n : ℕ) (i : Fin n) :
    targetOver G n ≫ composableπ G n i = sourceCechRightDivision G (op ⦋n⦌) i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      unfold targetOver
      rw [ofComposableArrows_π]
      let x : Fin (n + 2) → G.groupoidPoints (sourceCechOver G (op ⦋n + 1⦌)) :=
        fun j => sourceCechπOver G (op ⦋n + 1⦌) j.rev ≫ G.t
      let a : ∀ j : Fin (n + 1), x j.castSucc ⟶ x j.succ := fun j =>
        PointHom.ofArrow (sourceCechRightDivision G (op ⦋n + 1⦌) j.rev)
          (by simpa only [x, Fin.rev_castSucc] using
            sourceCechRightDivision_source G (op ⦋n + 1⦌) j.rev)
          (by simpa only [x, Fin.rev_succ] using
            sourceCechRightDivision_target G (op ⦋n + 1⦌) j.rev)
      change ((ComposableArrows.mkOfObjOfMapSucc x a).map' i.rev.val (i.rev.val + 1)).arrow = _
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ x a i.rev.val i.rev.isLt]
      change sourceCechRightDivision G (op ⦋n + 1⦌) i.rev.rev = _
      rw [Fin.rev_rev]

/-- Simplex operators intertwine the scheme-level components of `t_•`. -/
private theorem targetSimplicial_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (Scheme.Hom.simplicialScheme G.s.left).map f ≫
          (targetOver G m.unop.len).left ≫ composableComparison G m.unop.len =
        ((targetOver G n.unop.len).left ≫ composableComparison G n.unop.len) ≫
          (simplicialScheme G).map f :=
  sorry

/-- The cartesian morphism `t_• : (R/U)_• ⟶ X` associated to a groupoid scheme. -/
def targetSimplicial : Scheme.Hom.simplicialScheme G.s.left ⟶ simplicialScheme G where
  app n := (targetOver G n.unop.len).left ≫ composableComparison G n.unop.len
  naturality := by exact targetSimplicial_naturality G

open scoped SimplexCategory.Truncated in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison to the coskeleton recovers the original term in the truncation range. -/
private theorem composableComparison_counit (n : ℕ) (hn : n ≤ 2) :
    composableComparisonOver G n ≫ (degreewiseCounitIso G hn).hom =
      𝟙 (composable G n) := by
  unfold composableComparisonOver degreewiseCounitIso
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  change limit.lift _ (composableMatchingCone G n) ≫
    limit.π _ (StructuredArrow.mk
      (𝟙 ((SimplexCategory.Truncated.inclusion 2).op.obj (op ⦋n, hn⦌₂)))) = _
  rw [limit.lift_π]
  exact simplexMap_id G ⦋n⦌

set_option backward.isDefEq.respectTransparency false in
/-- After identifying degree `0` of `(R/U)_•` with `R` and degree `0` of `X` with `U`, the
component of `t_•` is the target map `t`. -/
theorem targetSimplicial_app_zero :
    (Arrow.cechNerve.degreeZero.iso (Arrow.mk G.s.left)).inv ≫
        (targetSimplicial G).app (op ⦋0⦌) ≫ (degreeZero.iso G).hom =
      G.t.left := by
  have hcomp : composableComparison G 0 ≫ (degreeZero.iso G).hom = 𝟙 G.U.left :=
    congrArg (fun f => f.left) (composableComparison_counit G 0 (by decide))
  change ((Arrow.cechNerve.degreeZero.iso (Arrow.mk G.s.left)).inv) ≫
    ((targetOver G 0).left ≫ composableComparison G 0) ≫ (degreeZero.iso G).hom = _
  rw [Category.assoc, hcomp]
  erw [Category.comp_id, targetOver_zero]
  exact Arrow.cechNerve.degreeZero.inv_π_assoc (Arrow.mk G.s.left) G.t.left

set_option backward.isDefEq.respectTransparency false in
/-- After identifying degree `1` of `(R/U)_•` with `pullback s s` and degree `1` of `X` with `R`,
the component of `t_•` is right division `(r₀, r₁) ↦ r₀ ∘ r₁⁻¹`. -/
theorem targetSimplicial_app_one :
    (Arrow.cechNerve.degreeOne.pullbackIso (Arrow.mk G.s.left)).inv ≫
        (targetSimplicial G).app (op ⦋1⦌) ≫ (degreeOne.iso G).hom =
      (PreservesPullback.iso (Over.forget S) G.s G.s).inv ≫ G.rightDivision.left := by
  have hp : sourceCechπOver G (op ⦋1⦌) 0 ≫ G.s =
      sourceCechπOver G (op ⦋1⦌) 1 ≫ G.s := by
    apply Over.OverMorphism.ext
    exact (WidePullback.π_arrow (fun _ => G.s.left) (0 : Fin 2)).trans
      (WidePullback.π_arrow (fun _ => G.s.left) (1 : Fin 2)).symm
  let q : sourceCechOver G (op ⦋1⦌) ⟶ pullback G.s G.s :=
    pullback.lift (sourceCechπOver G (op ⦋1⦌) 0) (sourceCechπOver G (op ⦋1⦌) 1) hp
  have hqfst : q ≫ pullback.fst G.s G.s = sourceCechπOver G (op ⦋1⦌) 0 :=
    pullback.lift_fst _ _ _
  have hqsnd : q ≫ pullback.snd G.s G.s = sourceCechπOver G (op ⦋1⦌) 1 :=
    pullback.lift_snd _ _ _
  have hd : sourceCechRightDivision G (op ⦋1⦌) 0 = q ≫ G.rightDivision := by
    unfold sourceCechRightDivision rightDivision compose
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp [q, Category.assoc]
    · simp [q, Category.assoc]
  have hq : q.left ≫ (PreservesPullback.iso (Over.forget S) G.s G.s).hom =
      (Arrow.cechNerve.degreeOne.pullbackIso (Arrow.mk G.s.left)).hom := by
    apply pullback.hom_ext
    · erw [Category.assoc, PreservesPullback.iso_hom_fst,
        Arrow.cechNerve.degreeOne.pullbackIso.hom_fst]
      exact congrArg (fun f => f.left) hqfst
    · erw [Category.assoc, PreservesPullback.iso_hom_snd,
        Arrow.cechNerve.degreeOne.pullbackIso.hom_snd]
      exact congrArg (fun f => f.left) hqsnd
  have hqinv : (Arrow.cechNerve.degreeOne.pullbackIso (Arrow.mk G.s.left)).inv ≫ q.left =
      (PreservesPullback.iso (Over.forget S) G.s G.s).inv := by
    apply (cancel_mono (PreservesPullback.iso (Over.forget S) G.s G.s).hom).1
    rw [Category.assoc, hq, Iso.inv_hom_id, Iso.inv_hom_id]
  have hcomp : composableComparison G 1 ≫ (degreeOne.iso G).hom = 𝟙 G.R.left :=
    congrArg (fun f => f.left) (composableComparison_counit G 1 (by decide))
  change (Arrow.cechNerve.degreeOne.pullbackIso (Arrow.mk G.s.left)).inv ≫
    ((targetOver G 1).left ≫ composableComparison G 1) ≫ (degreeOne.iso G).hom = _
  rw [Category.assoc, hcomp]
  erw [Category.comp_id, targetOver_one, hd]
  change (Arrow.cechNerve.degreeOne.pullbackIso (Arrow.mk G.s.left)).inv ≫
    (q.left ≫ G.rightDivision.left) = _
  rw [← Category.assoc, hqinv]

set_option backward.isDefEq.respectTransparency false in
/-- After identifying degree `2` of `X` with `R ×_{s,U,t} R`, the first factor of `t_•` is
`r₀ ∘ r₁⁻¹`. -/
theorem targetSimplicial_app_two_fst :
    (targetSimplicial G).app (op ⦋2⦌) ≫ (degreeTwo.iso G).hom ≫ (pullback.fst G.s G.t).left =
      (sourceCechRightDivision G (op ⦋2⦌) 0).left := by
  have hcomp : composableComparison G 2 ≫ (degreeTwo.iso G).hom =
      𝟙 (composable G 2).left :=
    congrArg (fun f => f.left) (composableComparison_counit G 2 (by decide))
  change ((targetOver G 2).left ≫ composableComparison G 2) ≫
    (degreeTwo.iso G).hom ≫ (pullback.fst G.s G.t).left = _
  rw [Category.assoc, ← Category.assoc (composableComparison G 2), hcomp, Category.id_comp]
  exact congrArg (fun f => f.left) (targetSimplicial_π G 2 0)

set_option backward.isDefEq.respectTransparency false in
/-- After identifying degree `2` of `X` with `R ×_{s,U,t} R`, the second factor of `t_•` is
`r₁ ∘ r₂⁻¹`. -/
theorem targetSimplicial_app_two_snd :
    (targetSimplicial G).app (op ⦋2⦌) ≫ (degreeTwo.iso G).hom ≫ (pullback.snd G.s G.t).left =
      (sourceCechRightDivision G (op ⦋2⦌) 1).left := by
  have hcomp : composableComparison G 2 ≫ (degreeTwo.iso G).hom =
      𝟙 (composable G 2).left :=
    congrArg (fun f => f.left) (composableComparison_counit G 2 (by decide))
  change ((targetOver G 2).left ≫ composableComparison G 2) ≫
    (degreeTwo.iso G).hom ≫ (pullback.snd G.s G.t).left = _
  rw [Category.assoc, ← Category.assoc (composableComparison G 2), hcomp, Category.id_comp]
  exact congrArg (fun f => f.left) (targetSimplicial_π G 2 1)

/-- Every simplex-operator naturality square of the target morphism from the source Čech
nerve to the groupoid nerve is a pullback. -/
theorem targetSimplicial_isPullback {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    IsPullback ((targetSimplicial G).app n)
      ((Scheme.Hom.simplicialScheme G.s.left).map f)
      ((simplicialScheme G).map f) ((targetSimplicial G).app m) :=
  sorry

end AlgebraicGeometry.GroupoidScheme
