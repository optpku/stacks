/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer

/-!
# The stabilizer diagram of a groupoid scheme

This module constructs the canonical diagram comparing pairs of arrows in a groupoid scheme
with the fibres of its stabilizer.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The source fibre `R ×_{s, U} U` of a groupoid scheme. -/
def sourceFiber {S : Scheme.{u}} (G : GroupoidScheme S) : Over S :=
  pullback G.s (𝟙 G.U)

/-- The self-pullback of the relation morphism of a groupoid scheme. -/
def relationSelfPullback {S : Scheme.{u}} (G : GroupoidScheme S) : Over S :=
  pullback G.toPreRelation.hom G.toPreRelation.hom

/-- The structure morphism from the stabilizer to the object scheme. -/
def stabilizerMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizer.X.left ⟶ G.U :=
  G.stabilizer.X.hom

/-- The fibre product `R ×_{s, U} G` with the stabilizer. -/
def stabilizerFiber {S : Scheme.{u}} (G : GroupoidScheme S) : Over S :=
  pullback G.s G.stabilizerMap

/-- The identity on the arrow scheme and the source map agree over the object scheme. -/
theorem sourceUnitMap_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (𝟙 G.R) ≫ G.s = G.s ≫ 𝟙 G.U := sorry

/-- The canonical map `f ↦ (f, s(f))` into the source fibre. -/
def sourceUnitMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.R ⟶ G.sourceFiber :=
  pullback.lift (𝟙 G.R) G.s G.sourceUnitMap_condition

/-- The first projection from the source fibre to the arrow scheme. -/
def sourceUnitInverse {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceFiber ⟶ G.R :=
  pullback.fst G.s (𝟙 G.U)

/-- The first projection of the source-unit map is the identity. -/
theorem sourceUnitMap_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitMap ≫ G.sourceUnitInverse = 𝟙 G.R := sorry

/-- The second projection of the source-unit map is the source map. -/
theorem sourceUnitMap_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitMap ≫ pullback.snd G.s (𝟙 G.U) = G.s := sorry

/-- The first projection followed by the source-unit map is the identity. -/
theorem sourceUnitInverse_sourceUnitMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitInverse ≫ G.sourceUnitMap = 𝟙 G.sourceFiber := sorry

/-- The stabilizer unit and its structure morphism agree with the first source projection. -/
theorem unitBaseChangeMap_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.s (𝟙 G.U) ≫ G.s =
      (pullback.snd G.s (𝟙 G.U) ≫ stabilizerOneLift G) ≫ G.stabilizerMap := sorry

/-- The base change of the stabilizer unit along the source map. -/
def unitBaseChangeMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceFiber ⟶ G.stabilizerFiber :=
  pullback.lift (pullback.fst G.s (𝟙 G.U))
    (pullback.snd G.s (𝟙 G.U) ≫ stabilizerOneLift G) G.unitBaseChangeMap_condition

/-- The projection from the source fibre to the object scheme. -/
def sourceProjection {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceFiber ⟶ G.U :=
  pullback.snd G.s (𝟙 G.U)

/-- The projection from the stabilizer fibre to the stabilizer carrier. -/
def stabilizerProjection {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizerFiber ⟶ G.stabilizer.X.left :=
  pullback.snd G.s G.stabilizerMap

/-- The inverse of the first arrow and the second arrow in a relation pair are composable. -/
theorem differenceArrow_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.i) ≫ G.s =
      pullback.snd G.toPreRelation.hom G.toPreRelation.hom ≫ G.t := sorry

/-- The loop `f⁻¹ ∘ g` associated to two arrows with equal source and target. -/
def differenceArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.relationSelfPullback ⟶ G.R :=
  pullback.lift
      (pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.i)
      (pullback.snd G.toPreRelation.hom G.toPreRelation.hom)
      G.differenceArrow_condition ≫ G.c

/-- The difference loop has relation map equal to the diagonal of its base point. -/
theorem differenceToStabilizer_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceArrow ≫ G.toPreRelation.hom =
      (pullback.snd G.toPreRelation.hom G.toPreRelation.hom ≫ G.s) ≫
        diag G.U := sorry

/-- The difference loop regarded as an element of the stabilizer. -/
def differenceToStabilizer {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.relationSelfPullback ⟶ G.stabilizer.X.left :=
  pullback.lift G.differenceArrow
    (pullback.snd G.toPreRelation.hom G.toPreRelation.hom ≫ G.s)
    G.differenceToStabilizer_condition

/-- The first arrow and the difference loop have the same source. -/
theorem differenceMap_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.s =
      G.differenceToStabilizer ≫ G.stabilizerMap := sorry

/-- The canonical map `(f, g) ↦ (f, f⁻¹ ∘ g)` into the stabilizer fibre. -/
def differenceMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.relationSelfPullback ⟶ G.stabilizerFiber :=
  pullback.lift (pullback.fst G.toPreRelation.hom G.toPreRelation.hom)
    G.differenceToStabilizer G.differenceMap_condition

/-- The first projection of the difference map is the first arrow. -/
theorem differenceMap_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceMap ≫ pullback.fst G.s G.stabilizerMap =
      pullback.fst G.toPreRelation.hom G.toPreRelation.hom := sorry

/-- The second projection of the difference map is the stabilizer-valued difference. -/
theorem differenceMap_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceMap ≫ pullback.snd G.s G.stabilizerMap =
      G.differenceToStabilizer := sorry

/-- The first arrow and its stabilizer element are composable. -/
theorem translateArrow_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.s G.stabilizerMap ≫ G.s =
      (pullback.snd G.s G.stabilizerMap ≫
        pullback.fst G.toPreRelation.hom (diag G.U)) ≫ G.t := sorry

/-- Stabilizer translation sends `(f, h)` to the arrow `f ∘ h`. -/
def translateArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizerFiber ⟶ G.R :=
  pullback.lift (pullback.fst G.s G.stabilizerMap)
      (pullback.snd G.s G.stabilizerMap ≫
        pullback.fst G.toPreRelation.hom (diag G.U))
      G.translateArrow_condition ≫ G.c

/-- An arrow and its stabilizer translate have the same relation map. -/
theorem translateMap_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.s G.stabilizerMap ≫ G.toPreRelation.hom =
      G.translateArrow ≫ G.toPreRelation.hom := sorry

/-- The translation map `(f, h) ↦ (f, f ∘ h)` from the stabilizer fibre. -/
def translateMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizerFiber ⟶ G.relationSelfPullback :=
  pullback.lift (pullback.fst G.s G.stabilizerMap)
    G.translateArrow G.translateMap_condition

/-- Translation followed by difference is the identity on the stabilizer fibre. -/
theorem translateMap_differenceMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.translateMap ≫ G.differenceMap = 𝟙 G.stabilizerFiber := sorry

/-- Difference followed by translation is the identity on pairs of related arrows. -/
theorem differenceMap_translateMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceMap ≫ G.translateMap = 𝟙 G.relationSelfPullback := sorry

/-- The source-unit, diagonal, unit-base-change, and difference maps form a commutative square. -/
theorem stabilizerDiagram_comm {S : Scheme.{u}} (G : GroupoidScheme S) :
    CommSq G.sourceUnitMap (pullback.diagonal G.toPreRelation.hom)
      G.unitBaseChangeMap G.differenceMap := sorry

/-- The source-unit map and its first-projection inverse form an isomorphism. -/
def sourceUnitIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.R ≅ G.sourceFiber where
  hom := G.sourceUnitMap
  inv := G.sourceUnitInverse
  hom_inv_id := G.sourceUnitMap_fst
  inv_hom_id := G.sourceUnitInverse_sourceUnitMap

/-- The forward morphism of the source-unit isomorphism is the source-unit map. -/
theorem sourceUnitIso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitIso.hom = G.sourceUnitMap := sorry

/-- The inverse morphism of the source-unit isomorphism is the first pullback projection. -/
theorem sourceUnitIso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitIso.inv = G.sourceUnitInverse := sorry

/-- The difference and translation maps form an isomorphism. -/
def differenceIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.relationSelfPullback ≅ G.stabilizerFiber where
  hom := G.differenceMap
  inv := G.translateMap
  hom_inv_id := G.differenceMap_translateMap
  inv_hom_id := G.translateMap_differenceMap

/-- The forward morphism of the difference isomorphism is the difference map. -/
theorem differenceIso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceIso.hom = G.differenceMap := sorry

/-- The inverse morphism of the difference isomorphism is stabilizer translation. -/
theorem differenceIso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceIso.inv = G.translateMap := sorry

/-- The unit square between the source fibre and stabilizer fibre is a pullback square. -/
theorem unitSquare_isPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback G.sourceProjection G.unitBaseChangeMap
      (stabilizerOneLift G) G.stabilizerProjection := sorry

end AlgebraicGeometry.GroupoidScheme
