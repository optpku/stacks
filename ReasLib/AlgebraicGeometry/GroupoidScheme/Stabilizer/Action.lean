/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer

/-!
# The stabilizer action on groupoid arrows

The stabilizer of a groupoid scheme acts on its arrow scheme over the target by groupoid
composition.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj MonoidalLeftAction

noncomputable section

-- The action uses definitionally equal slice and pullback objects in its morphism types.
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The arrow scheme of `G`, regarded as an object over `G.U` through the target map. -/
def arrowsOverTarget : Over G.U :=
  Over.mk G.t

/-- The structure map of `arrowsOverTarget G` is the target map of `G`. -/
theorem arrowsOverTarget_hom :
    (arrowsOverTarget G).hom = G.t := rfl

/-- The stabilizer component of a pair in
`G.stabilizer.X ⊗ arrowsOverTarget G`, included in the arrow scheme. -/
def actionFirst :
    (G.stabilizer.X ⊗ arrowsOverTarget G).left ⟶ G.R :=
  (fst G.stabilizer.X (arrowsOverTarget G)).left ≫
    G.toPreRelation.stabilizerToArrows

/-- The arrow component of a pair in `G.stabilizer.X ⊗ arrowsOverTarget G`. -/
def actionSecond :
    (G.stabilizer.X ⊗ arrowsOverTarget G).left ⟶ G.R :=
  (snd G.stabilizer.X (arrowsOverTarget G)).left

private theorem action_stabilizer_source :
    G.toPreRelation.stabilizerToArrows ≫ G.s = G.stabilizer.X.hom := by
  have h := congrArg (fun k => k ≫ prod.snd)
    (pullback.condition (f := G.toPreRelation.hom) (g := diag G.U))
  change pullback.fst G.toPreRelation.hom (diag G.U) ≫ G.s =
    pullback.snd G.toPreRelation.hom (diag G.U)
  simpa only [Category.assoc, show G.toPreRelation.hom ≫ prod.snd = G.s from
    prod.lift_snd _ _, prod.lift_snd, Category.comp_id] using h

private theorem action_stabilizer_target :
    G.toPreRelation.stabilizerToArrows ≫ G.t = G.stabilizer.X.hom := by
  have h := congrArg (fun k => k ≫ prod.fst)
    (pullback.condition (f := G.toPreRelation.hom) (g := diag G.U))
  change pullback.fst G.toPreRelation.hom (diag G.U) ≫ G.t =
    pullback.snd G.toPreRelation.hom (diag G.U)
  simpa only [Category.assoc, show G.toPreRelation.hom ≫ prod.fst = G.t from
    prod.lift_fst _ _, prod.lift_fst, Category.comp_id] using h

/-- A stabilizer arrow and an arrow over the same target form a composable pair. -/
theorem actionPair_condition :
    actionFirst G ≫ G.s = actionSecond G ≫ G.t := by
  dsimp only [actionFirst, actionSecond]
  rw [Category.assoc, action_stabilizer_source]
  exact (Over.w (fst G.stabilizer.X (arrowsOverTarget G))).trans
    (Over.w (snd G.stabilizer.X (arrowsOverTarget G))).symm

/-- The canonical map from the action product to the scheme of composable arrows. -/
def actionPair :
    (G.stabilizer.X ⊗ arrowsOverTarget G).left ⟶ pullback G.s G.t :=
  pullback.lift (actionFirst G) (actionSecond G) (actionPair_condition G)

/-- The first projection of `actionPair G` is the included stabilizer arrow. -/
theorem actionPair_fst :
    actionPair G ≫ pullback.fst G.s G.t = actionFirst G :=
  pullback.lift_fst _ _ _

/-- The second projection of `actionPair G` is the arrow being acted upon. -/
theorem actionPair_snd :
    actionPair G ≫ pullback.snd G.s G.t = actionSecond G :=
  pullback.lift_snd _ _ _

/-- Composition with a stabilizer arrow preserves the target of the acted-on arrow. -/
theorem actionHom_condition :
    (actionPair G ≫ G.c) ≫ G.t =
      (G.stabilizer.X ⊗ arrowsOverTarget G).hom := by
  rw [Category.assoc, G.comp_target, ← Category.assoc, actionPair_fst]
  dsimp only [actionFirst]
  rw [Category.assoc, action_stabilizer_target]
  exact Over.w (fst G.stabilizer.X (arrowsOverTarget G))

/-- The canonical action morphism induced by the groupoid composition `G.c`. -/
def actionHom :
    G.stabilizer.X ⊗ arrowsOverTarget G ⟶ arrowsOverTarget G :=
  Over.homMk (actionPair G ≫ G.c) (actionHom_condition G)

/-- The underlying scheme map of `actionHom G` is the composite induced by `G.c`. -/
theorem actionHom_left :
    (actionHom G).left = actionPair G ≫ G.c := rfl

/-- The action morphism satisfies the identity-action law. -/
theorem actionHom_one_smul :
    η[G.stabilizer.X] ⊵ₗ arrowsOverTarget G ≫ actionHom G =
      (λₗ (arrowsOverTarget G)).hom := by
  change (η[G.stabilizer.X] ▷ arrowsOverTarget G) ≫ actionHom G =
    (λ_ (arrowsOverTarget G)).hom
  apply Over.OverMorphism.ext
  let r := (snd (𝟙_ (Over G.U)) (arrowsOverTarget G)).left
  have hunit : η[G.stabilizer.X].left ≫ G.toPreRelation.stabilizerToArrows = G.e :=
    pullback.lift_fst _ _ _
  have hbase : (fst (𝟙_ (Over G.U)) (arrowsOverTarget G)).left = r ≫ G.t := by
    change pullback.fst (𝟙 G.U) G.t = pullback.snd (𝟙 G.U) G.t ≫ G.t
    simpa only [Category.comp_id] using
      (pullback.condition (f := 𝟙 G.U) (g := G.t))
  have h : ((r ≫ G.t) ≫ G.e) ≫ G.s = r ≫ G.t := by
    simp only [Category.assoc, G.identity_source, Category.comp_id]
  have hpair : (η[G.stabilizer.X] ▷ arrowsOverTarget G).left ≫ actionPair G =
      pullback.lift ((r ≫ G.t) ≫ G.e) r h := by
    apply pullback.hom_ext
    · calc
        _ = (fst (𝟙_ (Over G.U)) (arrowsOverTarget G)).left ≫
            η[G.stabilizer.X].left ≫ G.toPreRelation.stabilizerToArrows := by
              simp [Category.assoc, actionPair_fst, actionFirst]
        _ = (fst (𝟙_ (Over G.U)) (arrowsOverTarget G)).left ≫ G.e := by
          rw [hunit]
        _ = _ := by rw [hbase, pullback.lift_fst]
    · simp [Category.assoc, actionPair_snd, actionSecond, r]
  change (η[G.stabilizer.X] ▷ arrowsOverTarget G).left ≫ (actionPair G ≫ G.c) =
    (λ_ (arrowsOverTarget G)).hom.left
  calc
    _ = pullback.lift ((r ≫ G.t) ≫ G.e) r h ≫ G.c := by
      rw [← Category.assoc, hpair]
    _ = r := G.left_identity r h
    _ = _ := rfl

/-- The action morphism is compatible with stabilizer multiplication. -/
theorem actionHom_mul_smul :
    μ[G.stabilizer.X] ⊵ₗ arrowsOverTarget G ≫ actionHom G =
      (αₗ G.stabilizer.X G.stabilizer.X (arrowsOverTarget G)).hom ≫
        G.stabilizer.X ⊴ₗ actionHom G ≫ actionHom G := by
  change (μ[G.stabilizer.X] ▷ arrowsOverTarget G) ≫ actionHom G =
    (α_ G.stabilizer.X G.stabilizer.X (arrowsOverTarget G)).hom ≫
      (G.stabilizer.X ◁ actionHom G) ≫ actionHom G
  apply Over.OverMorphism.ext
  let p := (fst (G.stabilizer.X ⊗ G.stabilizer.X) (arrowsOverTarget G)).left
  let a := p ≫ (fst G.stabilizer.X G.stabilizer.X).left ≫
    G.toPreRelation.stabilizerToArrows
  let b := p ≫ (snd G.stabilizer.X G.stabilizer.X).left ≫
    G.toPreRelation.stabilizerToArrows
  let d := (snd (G.stabilizer.X ⊗ G.stabilizer.X) (arrowsOverTarget G)).left
  have hab : a ≫ G.s = b ≫ G.t := by
    dsimp only [a, b]
    simp only [Category.assoc, action_stabilizer_source, action_stabilizer_target, Over.w]
  have hbd : b ≫ G.s = d ≫ G.t := by
    dsimp only [b, d, p]
    simp only [Category.assoc, action_stabilizer_source, Over.w]
    exact (Over.w (snd (G.stabilizer.X ⊗ G.stabilizer.X) (arrowsOverTarget G))).symm
  have hab_d : (pullback.lift a b hab ≫ G.c) ≫ G.s = d ≫ G.t := by
    simpa only [Category.assoc, G.comp_source, pullback.lift_snd_assoc] using hbd
  have ha_bd : a ≫ G.s = (pullback.lift b d hbd ≫ G.c) ≫ G.t := by
    simpa only [Category.assoc, G.comp_target, pullback.lift_fst_assoc] using hab
  have hmul : μ[G.stabilizer.X].left ≫ G.toPreRelation.stabilizerToArrows =
      stabilizerComposablePair G ≫ G.c :=
    pullback.lift_fst _ _ _
  have hp : p ≫ stabilizerComposablePair G = pullback.lift a b hab := by
    apply pullback.hom_ext
    · simp [Category.assoc, stabilizerComposablePair, a, stabilizer]
    · simp [Category.assoc, stabilizerComposablePair, b, stabilizer]
  have hl : (μ[G.stabilizer.X] ▷ arrowsOverTarget G).left ≫ actionPair G =
      pullback.lift (pullback.lift a b hab ≫ G.c) d hab_d := by
    apply pullback.hom_ext
    · calc
        _ = p ≫ μ[G.stabilizer.X].left ≫
            G.toPreRelation.stabilizerToArrows := by
              simp [Category.assoc, actionPair_fst, actionFirst, p]
        _ = p ≫ stabilizerComposablePair G ≫ G.c := by rw [hmul]
        _ = _ := by rw [← Category.assoc, hp, pullback.lift_fst]
    · simp [Category.assoc, actionPair_snd, actionSecond, d]
  have hinner :
      (α_ G.stabilizer.X G.stabilizer.X (arrowsOverTarget G)).hom.left ≫
        (snd G.stabilizer.X (G.stabilizer.X ⊗ arrowsOverTarget G)).left ≫
          actionPair G = pullback.lift b d hbd := by
    apply pullback.hom_ext
    · simp [Category.assoc, actionPair_fst, actionFirst, b, p]
    · simp [Category.assoc, actionPair_snd, actionSecond, d]
  have hr :
      ((α_ G.stabilizer.X G.stabilizer.X (arrowsOverTarget G)).hom ≫
        (G.stabilizer.X ◁ actionHom G)).left ≫ actionPair G =
          pullback.lift a (pullback.lift b d hbd ≫ G.c) ha_bd := by
    apply pullback.hom_ext
    · simp [Category.assoc, actionPair_fst, actionFirst, a, p]
    · calc
        _ = ((α_ G.stabilizer.X G.stabilizer.X (arrowsOverTarget G)).hom.left ≫
            (snd G.stabilizer.X (G.stabilizer.X ⊗ arrowsOverTarget G)).left ≫
              actionPair G) ≫ G.c := by
                simp [Category.assoc, actionPair_snd, actionSecond, actionHom_left]
        _ = pullback.lift b d hbd ≫ G.c := by rw [hinner]
        _ = _ := (pullback.lift_snd _ _ _).symm
  change (μ[G.stabilizer.X] ▷ arrowsOverTarget G).left ≫ (actionPair G ≫ G.c) =
    (α_ G.stabilizer.X G.stabilizer.X (arrowsOverTarget G)).hom.left ≫
      (G.stabilizer.X ◁ actionHom G).left ≫ (actionPair G ≫ G.c)
  calc
    _ = pullback.lift (pullback.lift a b hab ≫ G.c) d hab_d ≫ G.c := by
      rw [← Category.assoc, hl]
    _ = pullback.lift a (pullback.lift b d hbd ≫ G.c) ha_bd ≫ G.c :=
      G.associativity a b d hab hbd hab_d ha_bd
    _ = _ := by
      simpa only [Over.comp_left, Category.assoc] using
        congrArg (fun k => k ≫ G.c) hr.symm

/-- The module-object structure on arrows over the target induced by `actionHom G`. -/
@[reducible]
def actionModObj : ModObj G.stabilizer.X (arrowsOverTarget G) where
  smul := actionHom G
  one_smul := actionHom_one_smul G
  mul_smul := actionHom_mul_smul G

/-- The canonical action of the stabilizer on arrows over the target. -/
def stabilizerAction : Mod (Over G.U) G.stabilizer.X where
  X := arrowsOverTarget G
  mod := actionModObj G

/-- The object underlying `stabilizerAction G` is the arrow scheme over the target. -/
theorem stabilizerAction_X :
    (stabilizerAction G).X = arrowsOverTarget G := rfl

/-- The stored action morphism of `stabilizerAction G` is `actionHom G`. -/
theorem stabilizerAction_smul :
    (stabilizerAction G).mod.smul = actionHom G := rfl

end AlgebraicGeometry.GroupoidScheme
