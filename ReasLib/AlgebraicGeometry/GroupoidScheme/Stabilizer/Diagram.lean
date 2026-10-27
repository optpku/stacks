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

-- The diagram uses definitionally equal slice and pullback objects in its morphism types.
set_option backward.isDefEq.respectTransparency false

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
    (𝟙 G.R) ≫ G.s = G.s ≫ 𝟙 G.U := by simp

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
    G.sourceUnitMap ≫ G.sourceUnitInverse = 𝟙 G.R :=
  pullback.lift_fst _ _ _

/-- The second projection of the source-unit map is the source map. -/
theorem sourceUnitMap_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitMap ≫ pullback.snd G.s (𝟙 G.U) = G.s :=
  pullback.lift_snd _ _ _

/-- The first projection followed by the source-unit map is the identity. -/
theorem sourceUnitInverse_sourceUnitMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitInverse ≫ G.sourceUnitMap = 𝟙 G.sourceFiber := by
  dsimp only [sourceFiber, sourceUnitInverse, sourceUnitMap]
  apply pullback.hom_ext
  · simp [Category.assoc]
  · simpa [Category.assoc, pullback.lift_snd] using
      (pullback.condition (f := G.s) (g := 𝟙 G.U))

/-- The stabilizer unit and its structure morphism agree with the first source projection. -/
theorem unitBaseChangeMap_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.s (𝟙 G.U) ≫ G.s =
      (pullback.snd G.s (𝟙 G.U) ≫ stabilizerOneLift G) ≫ G.stabilizerMap := by
  have hu : stabilizerOneLift G ≫ G.stabilizerMap = 𝟙 G.U :=
    pullback.lift_snd _ _ _
  rw [Category.assoc, hu]
  exact pullback.condition

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

private theorem diagram_relation_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.hom ≫ prod.fst = G.t :=
  prod.lift_fst _ _

private theorem diagram_relation_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.hom ≫ prod.snd = G.s :=
  prod.lift_snd _ _

private theorem relationPair_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.s =
      pullback.snd G.toPreRelation.hom G.toPreRelation.hom ≫ G.s := by
  have h := congrArg (fun k => k ≫ prod.snd)
    (pullback.condition (f := G.toPreRelation.hom) (g := G.toPreRelation.hom))
  simpa only [Category.assoc, diagram_relation_snd G] using h

private theorem relationPair_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.t =
      pullback.snd G.toPreRelation.hom G.toPreRelation.hom ≫ G.t := by
  have h := congrArg (fun k => k ≫ prod.fst)
    (pullback.condition (f := G.toPreRelation.hom) (g := G.toPreRelation.hom))
  simpa only [Category.assoc, diagram_relation_fst G] using h

private theorem stabilizerArrow_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.toPreRelation.hom (diag G.U) ≫ G.s = G.stabilizerMap := by
  have h := congrArg (fun k => k ≫ prod.snd)
    (pullback.condition (f := G.toPreRelation.hom) (g := diag G.U))
  change pullback.fst G.toPreRelation.hom (diag G.U) ≫ G.s =
    pullback.snd G.toPreRelation.hom (diag G.U)
  simpa only [Category.assoc, diagram_relation_snd G, prod.lift_snd,
    Category.comp_id] using h

private theorem stabilizerArrow_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.toPreRelation.hom (diag G.U) ≫ G.t = G.stabilizerMap := by
  have h := congrArg (fun k => k ≫ prod.fst)
    (pullback.condition (f := G.toPreRelation.hom) (g := diag G.U))
  change pullback.fst G.toPreRelation.hom (diag G.U) ≫ G.t =
    pullback.snd G.toPreRelation.hom (diag G.U)
  simpa only [Category.assoc, diagram_relation_fst G, prod.lift_fst,
    Category.comp_id] using h

/-- The inverse of the first arrow and the second arrow in a relation pair are composable. -/
theorem differenceArrow_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.i) ≫ G.s =
      pullback.snd G.toPreRelation.hom G.toPreRelation.hom ≫ G.t := by
  calc
    _ = pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ (G.i ≫ G.s) :=
      Category.assoc _ _ _
    _ = pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.t :=
      congrArg (fun k => pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ k)
        G.inverse_source
    _ = _ := relationPair_target G

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
        diag G.U := by
  apply prod.hom_ext
  · simp only [Category.assoc, diagram_relation_fst G, prod.lift_fst, Category.comp_id]
    dsimp only [differenceArrow, relationSelfPullback]
    simpa only [Category.assoc, G.comp_target, G.inverse_target,
      pullback.lift_fst_assoc] using relationPair_source G
  · simp only [Category.assoc, diagram_relation_snd G, prod.lift_snd, Category.comp_id]
    dsimp only [differenceArrow, relationSelfPullback]
    simp only [Category.assoc, G.comp_source, pullback.lift_snd_assoc]

/-- The difference loop regarded as an element of the stabilizer. -/
def differenceToStabilizer {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.relationSelfPullback ⟶ G.stabilizer.X.left :=
  pullback.lift G.differenceArrow
    (pullback.snd G.toPreRelation.hom G.toPreRelation.hom ≫ G.s)
    G.differenceToStabilizer_condition

/-- The first arrow and the difference loop have the same source. -/
theorem differenceMap_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.s =
      G.differenceToStabilizer ≫ G.stabilizerMap := by
  exact (relationPair_source G).trans (pullback.lift_snd _ _ _).symm

/-- The canonical map `(f, g) ↦ (f, f⁻¹ ∘ g)` into the stabilizer fibre. -/
def differenceMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.relationSelfPullback ⟶ G.stabilizerFiber :=
  pullback.lift (pullback.fst G.toPreRelation.hom G.toPreRelation.hom)
    G.differenceToStabilizer G.differenceMap_condition

/-- The first projection of the difference map is the first arrow. -/
theorem differenceMap_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceMap ≫ pullback.fst G.s G.stabilizerMap =
      pullback.fst G.toPreRelation.hom G.toPreRelation.hom :=
  pullback.lift_fst _ _ _

/-- The second projection of the difference map is the stabilizer-valued difference. -/
theorem differenceMap_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceMap ≫ pullback.snd G.s G.stabilizerMap =
      G.differenceToStabilizer :=
  pullback.lift_snd _ _ _

/-- The first arrow and its stabilizer element are composable. -/
theorem translateArrow_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.s G.stabilizerMap ≫ G.s =
      (pullback.snd G.s G.stabilizerMap ≫
        pullback.fst G.toPreRelation.hom (diag G.U)) ≫ G.t := by
  calc
    _ = pullback.snd G.s G.stabilizerMap ≫ G.stabilizerMap := pullback.condition
    _ = pullback.snd G.s G.stabilizerMap ≫
        (pullback.fst G.toPreRelation.hom (diag G.U) ≫ G.t) :=
      congrArg (fun k => pullback.snd G.s G.stabilizerMap ≫ k)
        (stabilizerArrow_target G).symm
    _ = _ := (Category.assoc _ _ _).symm

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
      G.translateArrow ≫ G.toPreRelation.hom := by
  apply prod.hom_ext
  · simp only [Category.assoc, diagram_relation_fst G]
    dsimp only [translateArrow, stabilizerFiber]
    simp only [Category.assoc, G.comp_target, pullback.lift_fst_assoc]
  · simp only [Category.assoc, diagram_relation_snd G]
    dsimp only [translateArrow, stabilizerFiber]
    simpa only [Category.assoc, G.comp_source, pullback.lift_snd_assoc,
      stabilizerArrow_source G] using
      (pullback.condition (f := G.s) (g := G.stabilizerMap))

/-- The translation map `(f, h) ↦ (f, f ∘ h)` from the stabilizer fibre. -/
def translateMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizerFiber ⟶ G.relationSelfPullback :=
  pullback.lift (pullback.fst G.s G.stabilizerMap)
    G.translateArrow G.translateMap_condition

@[reassoc]
private theorem diagram_comp_lift {S : Scheme.{u}} {W X Y Z V : Over S}
    {f : X ⟶ Z} {g : Y ⟶ Z} (k : V ⟶ W) (a : W ⟶ X) (b : W ⟶ Y)
    (h : a ≫ f = b ≫ g) :
    k ≫ pullback.lift a b h =
      pullback.lift (k ≫ a) (k ≫ b) (by simp only [Category.assoc, h]) := by
  apply pullback.hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc]

private theorem diagram_compose_congr {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {a a' b b' : T ⟶ G.R}
    (h : a ≫ G.s = b ≫ G.t) (h' : a' ≫ G.s = b' ≫ G.t)
    (ha : a = a') (hb : b = b') : G.compose a b h = G.compose a' b' h' := by
  subst a'
  subst b'
  rfl

private theorem diagram_inv_comp_cancel {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (a b : T ⟶ G.R) (h : a ≫ G.s = b ≫ G.t)
    (h' : (a ≫ G.i) ≫ G.s = G.compose a b h ≫ G.t) :
    G.compose (a ≫ G.i) (G.compose a b h) h' = b := by
  have hi : (a ≫ G.i) ≫ G.s = a ≫ G.t := by
    simp [Category.assoc, G.inverse_source]
  have hib : G.compose (a ≫ G.i) a hi ≫ G.s = b ≫ G.t := by
    simpa [compose, Category.assoc, G.comp_source, pullback.lift_snd_assoc] using h
  have heq : G.compose (a ≫ G.i) a hi = (b ≫ G.t) ≫ G.e :=
    (G.comp_inverse a hi).trans (congrArg (fun k => k ≫ G.e) h)
  calc
    _ = G.compose (G.compose (a ≫ G.i) a hi) b hib :=
      (G.associativity (a ≫ G.i) a b hi h hib h').symm
    _ = G.compose ((b ≫ G.t) ≫ G.e) b
        (by simp [Category.assoc, G.identity_source]) :=
      diagram_compose_congr G _ _ heq rfl
    _ = b := G.left_identity b _

private theorem diagram_comp_inv_cancel {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (a b : T ⟶ G.R) (h : (a ≫ G.i) ≫ G.s = b ≫ G.t)
    (h' : a ≫ G.s = G.compose (a ≫ G.i) b h ≫ G.t) :
    G.compose a (G.compose (a ≫ G.i) b h) h' = b := by
  have hi : a ≫ G.s = (a ≫ G.i) ≫ G.t := by
    simp [Category.assoc, G.inverse_target]
  have hab : G.compose a (a ≫ G.i) hi ≫ G.s = b ≫ G.t := by
    simpa [compose, Category.assoc, G.comp_source, pullback.lift_snd_assoc] using h
  have ht : a ≫ G.t = b ≫ G.t := by
    simpa [Category.assoc, G.inverse_source] using h
  have heq : G.compose a (a ≫ G.i) hi = (b ≫ G.t) ≫ G.e :=
    (G.inverse_comp a hi).trans (congrArg (fun k => k ≫ G.e) ht)
  calc
    _ = G.compose (G.compose a (a ≫ G.i) hi) b hab :=
      (G.associativity a (a ≫ G.i) b hi h hab h').symm
    _ = G.compose ((b ≫ G.t) ≫ G.e) b
        (by simp [Category.assoc, G.identity_source]) :=
      diagram_compose_congr G _ _ heq rfl
    _ = b := G.left_identity b _

private theorem translateMap_differenceArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.translateMap ≫ G.differenceArrow =
      pullback.snd G.s G.stabilizerMap ≫
        pullback.fst G.toPreRelation.hom (diag G.U) := by
  have h := diagram_inv_comp_cancel G
    (pullback.fst G.s G.stabilizerMap)
    (pullback.snd G.s G.stabilizerMap ≫
      pullback.fst G.toPreRelation.hom (diag G.U)) G.translateArrow_condition
    (by simp [compose, Category.assoc, G.inverse_source, G.comp_target])
  dsimp only [compose, translateMap, differenceArrow, translateArrow, stabilizerFiber,
    relationSelfPullback, toPreRelation, Scheme.PreRelation.ofHom, Over.mk_hom, Over.mk_left] at h ⊢
  simpa only [Category.assoc, diagram_comp_lift_assoc, diagram_comp_lift,
    pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc] using h

private theorem differenceMap_translateArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceMap ≫ G.translateArrow =
      pullback.snd G.toPreRelation.hom G.toPreRelation.hom := by
  have h := diagram_comp_inv_cancel G
    (pullback.fst G.toPreRelation.hom G.toPreRelation.hom)
    (pullback.snd G.toPreRelation.hom G.toPreRelation.hom) G.differenceArrow_condition
    (by simp [compose, Category.assoc, G.comp_target, G.inverse_target])
  dsimp only [compose, differenceMap, translateArrow, differenceToStabilizer,
    differenceArrow, stabilizerFiber, relationSelfPullback, toPreRelation,
    Scheme.PreRelation.ofHom, Over.mk_hom, Over.mk_left] at h ⊢
  simpa only [Category.assoc, diagram_comp_lift_assoc, diagram_comp_lift,
    pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
    pullback.lift_fst_assoc] using h

/-- Translation followed by difference is the identity on the stabilizer fibre. -/
theorem translateMap_differenceMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.translateMap ≫ G.differenceMap = 𝟙 G.stabilizerFiber := by
  apply pullback.hom_ext
  · dsimp only [translateMap, differenceMap, stabilizerFiber, relationSelfPullback]
    simp [Category.assoc]
  · change G.translateMap ≫ G.differenceMap ≫
        pullback.snd G.s G.stabilizerMap = pullback.snd G.s G.stabilizerMap
    rw [G.differenceMap_snd]
    apply pullback.hom_ext
    · simpa only [Category.assoc, differenceToStabilizer, pullback.lift_fst] using
        translateMap_differenceArrow G
    · change (G.translateMap ≫ G.differenceToStabilizer) ≫ G.stabilizerMap =
        pullback.snd G.s G.stabilizerMap ≫ G.stabilizerMap
      calc
        _ = G.translateMap ≫ (G.differenceToStabilizer ≫ G.stabilizerMap) :=
          Category.assoc _ _ _
        _ = G.translateMap ≫
            (pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.s) :=
          congrArg (fun k => G.translateMap ≫ k) G.differenceMap_condition.symm
        _ = pullback.fst G.s G.stabilizerMap ≫ G.s := by
          simp [translateMap]
        _ = _ := pullback.condition

/-- Difference followed by translation is the identity on pairs of related arrows. -/
theorem differenceMap_translateMap {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceMap ≫ G.translateMap = 𝟙 G.relationSelfPullback := by
  apply pullback.hom_ext
  · dsimp only [differenceMap, translateMap, stabilizerFiber, relationSelfPullback]
    simp [Category.assoc]
  · simpa only [Category.assoc, translateMap, pullback.lift_snd, Category.id_comp] using
      differenceMap_translateArrow G

private theorem diagonal_differenceArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.diagonal G.toPreRelation.hom ≫ G.differenceArrow = G.s ≫ G.e := by
  have hi : G.i ≫ G.s = (𝟙 G.R) ≫ G.t := by
    simpa using G.inverse_source
  have hp : pullback.diagonal G.toPreRelation.hom ≫
      pullback.lift
        (pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.i)
        (pullback.snd G.toPreRelation.hom G.toPreRelation.hom)
        G.differenceArrow_condition = pullback.lift G.i (𝟙 G.R) hi := by
    apply pullback.hom_ext
    · simp [Category.assoc]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd]
      rfl
  calc
    _ = (pullback.diagonal G.toPreRelation.hom ≫
        pullback.lift
          (pullback.fst G.toPreRelation.hom G.toPreRelation.hom ≫ G.i)
          (pullback.snd G.toPreRelation.hom G.toPreRelation.hom)
          G.differenceArrow_condition) ≫ G.c := (Category.assoc _ _ _).symm
    _ = pullback.lift G.i (𝟙 G.R) hi ≫ G.c := congrArg (fun k => k ≫ G.c) hp
    _ = G.s ≫ G.e := by simpa using G.comp_inverse (𝟙 G.R) (by simpa using hi)

/-- The source-unit, diagonal, unit-base-change, and difference maps form a commutative square. -/
theorem stabilizerDiagram_comm {S : Scheme.{u}} (G : GroupoidScheme S) :
    CommSq G.sourceUnitMap (pullback.diagonal G.toPreRelation.hom)
      G.unitBaseChangeMap G.differenceMap := by
  constructor
  apply pullback.hom_ext
  · dsimp only [sourceUnitMap, unitBaseChangeMap, differenceMap, sourceFiber,
      stabilizerFiber, relationSelfPullback]
    simp [Category.assoc]
  · change G.sourceUnitMap ≫ G.unitBaseChangeMap ≫
        pullback.snd G.s G.stabilizerMap =
      pullback.diagonal G.toPreRelation.hom ≫ G.differenceMap ≫
        pullback.snd G.s G.stabilizerMap
    rw [G.differenceMap_snd]
    dsimp only [unitBaseChangeMap]
    rw [pullback.lift_snd]
    apply pullback.hom_ext
    · have hs : (G.sourceUnitMap ≫ pullback.snd G.s (𝟙 G.U)) ≫ G.e =
          pullback.diagonal G.toPreRelation.hom ≫ G.differenceArrow :=
        (congrArg (fun k => k ≫ G.e) G.sourceUnitMap_snd).trans
          (diagonal_differenceArrow G).symm
      simpa only [Category.assoc, stabilizerOneLift, differenceToStabilizer,
        pullback.lift_fst] using hs
    · dsimp only [sourceUnitMap, stabilizerOneLift, differenceToStabilizer,
        sourceFiber, relationSelfPullback, toPreRelation, Scheme.PreRelation.ofHom,
        Over.mk_hom, Over.mk_left]
      simp [Category.assoc]

/-- The source-unit map and its first-projection inverse form an isomorphism. -/
def sourceUnitIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.R ≅ G.sourceFiber where
  hom := G.sourceUnitMap
  inv := G.sourceUnitInverse
  hom_inv_id := G.sourceUnitMap_fst
  inv_hom_id := G.sourceUnitInverse_sourceUnitMap

/-- The forward morphism of the source-unit isomorphism is the source-unit map. -/
theorem sourceUnitIso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitIso.hom = G.sourceUnitMap := rfl

/-- The inverse morphism of the source-unit isomorphism is the first pullback projection. -/
theorem sourceUnitIso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.sourceUnitIso.inv = G.sourceUnitInverse := rfl

/-- The difference and translation maps form an isomorphism. -/
def differenceIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.relationSelfPullback ≅ G.stabilizerFiber where
  hom := G.differenceMap
  inv := G.translateMap
  hom_inv_id := G.differenceMap_translateMap
  inv_hom_id := G.translateMap_differenceMap

/-- The forward morphism of the difference isomorphism is the difference map. -/
theorem differenceIso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceIso.hom = G.differenceMap := rfl

/-- The inverse morphism of the difference isomorphism is stabilizer translation. -/
theorem differenceIso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.differenceIso.inv = G.translateMap := rfl

/-- The unit square between the source fibre and stabilizer fibre is a pullback square. -/
theorem unitSquare_isPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback G.sourceProjection G.unitBaseChangeMap
      (stabilizerOneLift G) G.stabilizerProjection := by
  have hu : stabilizerOneLift G ≫ G.stabilizerMap = 𝟙 G.U :=
    pullback.lift_snd _ _ _
  have hf : G.unitBaseChangeMap ≫ pullback.fst G.s G.stabilizerMap =
      pullback.fst G.s (𝟙 G.U) := pullback.lift_fst _ _ _
  apply IsPullback.flip
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback G.s G.stabilizerMap)
  · rw [hf, hu]
    dsimp only [sourceFiber, sourceProjection]
    exact IsPullback.of_hasPullback G.s (𝟙 G.U)
  · exact pullback.lift_snd _ _ _

end AlgebraicGeometry.GroupoidScheme
