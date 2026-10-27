/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction

/-!
# Fibre-product presentation of restricted groupoid arrows

This module identifies the arrow scheme of a restricted groupoid scheme with the corresponding
iterated fibre product and records its projection formulas.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The arrow scheme in the iterated fibre-product presentation of a restriction. -/
abbrev iteratedPullbackArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) : Over S :=
  Limits.pullback (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t)

/-- The restricted arrow scheme maps canonically to `R ×_{s, U} U'`. -/
def pullbackToSourceSquare {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ Limits.pullback G.s g :=
  Limits.pullback.lift (pullbackArrow G g) (G.toPreRelation.pullback g).s
    (pullbackArrow_s G g)

/-- The two maps defining the canonical morphism to `U' ×_{U, t} R` commute. -/
theorem pullbackToTargetSquare_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).t ≫ g = pullbackArrow G g ≫ G.t := by
  change (Limits.pullback.snd (prod.lift G.t G.s) (prod.map g g) ≫ prod.fst) ≫ g =
    Limits.pullback.fst (prod.lift G.t G.s) (prod.map g g) ≫ G.t
  simpa only [Category.assoc, prod.map_fst, prod.lift_fst] using
    (congrArg (fun f ↦ f ≫ prod.fst)
      (Limits.pullback.condition (f := prod.lift G.t G.s) (g := prod.map g g))).symm

/-- The restricted arrow scheme maps canonically to `U' ×_{U, t} R`. -/
def pullbackToTargetSquare {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ Limits.pullback g G.t :=
  Limits.pullback.lift (G.toPreRelation.pullback g).t (pullbackArrow G g)
    (pullbackToTargetSquare_condition G g)

/-- The two square maps from the restricted arrow scheme have the same arrow projection. -/
theorem pullbackToIterated_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    pullbackToSourceSquare G g ≫ Limits.pullback.fst G.s g =
      pullbackToTargetSquare G g ≫ Limits.pullback.snd g G.t := by
  simp [pullbackToSourceSquare, pullbackToTargetSquare,
    Limits.pullback.lift_fst, Limits.pullback.lift_snd]

/-- The canonical map from the single-pullback arrow scheme to the displayed iterated
fibre product. -/
def pullbackToIterated {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ iteratedPullbackArrows G g :=
  Limits.pullback.lift (pullbackToSourceSquare G g) (pullbackToTargetSquare G g)
    (pullbackToIterated_condition G g)

/-- The arrow and endpoint projections from the displayed iterated fibre product satisfy
the single-pullback compatibility equation. -/
theorem iteratedToPullback_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst G.s g) ≫ G.toPreRelation.hom =
      prod.lift
          (Limits.pullback.snd (Limits.pullback.fst G.s g)
              (Limits.pullback.snd g G.t) ≫ Limits.pullback.fst g G.t)
          (Limits.pullback.fst (Limits.pullback.fst G.s g)
              (Limits.pullback.snd g G.t) ≫ Limits.pullback.snd G.s g) ≫
        prod.map g g := by
  change _ ≫ prod.lift G.t G.s = _
  apply prod.hom_ext
  · show _ ≫ prod.fst = _ ≫ prod.fst
    simp only [Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc]
    calc
      _ = (Limits.pullback.snd (Limits.pullback.fst G.s g)
          (Limits.pullback.snd g G.t) ≫ Limits.pullback.snd g G.t) ≫ G.t :=
        congrArg (fun f ↦ f ≫ G.t) Limits.pullback.condition
      _ = _ := by rw [Category.assoc, ← Limits.pullback.condition]
  · show _ ≫ prod.snd = _ ≫ prod.snd
    simp only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
    rw [Limits.pullback.condition]

/-- The canonical map from the displayed iterated fibre product to the single-pullback
arrow scheme. -/
def iteratedToPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    iteratedPullbackArrows G g ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift
    (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst G.s g)
    (prod.lift
      (Limits.pullback.snd (Limits.pullback.fst G.s g)
          (Limits.pullback.snd g G.t) ≫ Limits.pullback.fst g G.t)
      (Limits.pullback.fst (Limits.pullback.fst G.s g)
          (Limits.pullback.snd g G.t) ≫ Limits.pullback.snd G.s g))
    (iteratedToPullback_condition G g)

private theorem iteratedToPullback_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    iteratedToPullback G g ≫ pullbackArrow G g =
      Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst G.s g := by
  exact Limits.pullback.lift_fst _ _ _

private theorem iteratedToPullback_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    iteratedToPullback G g ≫ (G.toPreRelation.pullback g).t =
      Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst g G.t := by
  exact (Limits.pullback.lift_snd_assoc _ _ _ prod.fst).trans (prod.lift_fst _ _)

private theorem iteratedToPullback_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    iteratedToPullback G g ≫ (G.toPreRelation.pullback g).s =
      Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.snd G.s g := by
  exact (Limits.pullback.lift_snd_assoc _ _ _ prod.snd).trans (prod.lift_snd _ _)

/-- The canonical isomorphism from the restricted arrow scheme to the iterated fibre
product of the source and target pullback squares. -/
def pullbackArrowIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ≅ iteratedPullbackArrows G g where
  hom := pullbackToIterated G g
  inv := iteratedToPullback G g
  hom_inv_id := by
    apply Limits.pullback.hom_ext
    · change (pullbackToIterated G g ≫ iteratedToPullback G g) ≫ pullbackArrow G g =
        𝟙 _ ≫ pullbackArrow G g
      simp [Category.assoc, iteratedToPullback_arrow, pullbackToIterated,
        pullbackToSourceSquare, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc]
    · change (pullbackToIterated G g ≫ iteratedToPullback G g) ≫
          (G.toPreRelation.pullback g).hom = 𝟙 _ ≫ (G.toPreRelation.pullback g).hom
      apply prod.hom_ext
      · simp only [Category.assoc, Category.id_comp]
        change pullbackToIterated G g ≫ iteratedToPullback G g ≫
          (G.toPreRelation.pullback g).t = (G.toPreRelation.pullback g).t
        simp [iteratedToPullback_target, pullbackToIterated, pullbackToTargetSquare,
          Limits.pullback.lift_fst, Limits.pullback.lift_snd_assoc]
      · simp only [Category.assoc, Category.id_comp]
        change pullbackToIterated G g ≫ iteratedToPullback G g ≫
          (G.toPreRelation.pullback g).s = (G.toPreRelation.pullback g).s
        simp [iteratedToPullback_source, pullbackToIterated, pullbackToSourceSquare,
          Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc]
  inv_hom_id := by
    apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext
      · simp [Category.assoc, pullbackToIterated, pullbackToSourceSquare,
          Limits.pullback.lift_fst, iteratedToPullback_arrow]
      · simp [Category.assoc, pullbackToIterated, pullbackToSourceSquare,
          Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc,
          iteratedToPullback_source]
    · apply Limits.pullback.hom_ext
      · simp [Category.assoc, pullbackToIterated, pullbackToTargetSquare,
          Limits.pullback.lift_fst, Limits.pullback.lift_snd_assoc,
          iteratedToPullback_target]
      · simp [Category.assoc, pullbackToIterated, pullbackToTargetSquare,
          Limits.pullback.lift_snd, iteratedToPullback_arrow, Limits.pullback.condition]

/-- The `R`-projection through the upper fibre-product square agrees with the canonical
arrow projection. -/
theorem pullbackArrowIso_hom_upper_fst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst G.s g = pullbackArrow G g := by
  simp [pullbackArrowIso, pullbackToIterated, pullbackToSourceSquare,
    Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc]

/-- The `U'`-projection through the upper fibre-product square is the restricted source. -/
theorem pullbackArrowIso_hom_upper_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.snd G.s g = (G.toPreRelation.pullback g).s := by
  simp [pullbackArrowIso, pullbackToIterated, pullbackToSourceSquare,
    Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc]

/-- The `U'`-projection through the lower fibre-product square is the restricted target. -/
theorem pullbackArrowIso_hom_lower_fst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst g G.t = (G.toPreRelation.pullback g).t := by
  simp [pullbackArrowIso, pullbackToIterated, pullbackToTargetSquare,
    Limits.pullback.lift_fst, Limits.pullback.lift_snd_assoc]

/-- The `R`-projection through the lower fibre-product square agrees with the canonical
arrow projection. -/
theorem pullbackArrowIso_hom_lower_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.snd g G.t = pullbackArrow G g := by
  simp [pullbackArrowIso, pullbackToIterated, pullbackToTargetSquare,
    Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc]

end AlgebraicGeometry.GroupoidScheme

