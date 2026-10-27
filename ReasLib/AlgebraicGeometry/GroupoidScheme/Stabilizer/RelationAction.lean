/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Action
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

/-!
# The stabilizer action on the relation of a groupoid scheme

The stabilizer, base-changed to the product of the object scheme with itself, acts on the
arrow relation by groupoid composition. This action is a pseudo-torsor.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.RelationAction

variable {S : Scheme.{u}} (Q : GroupoidScheme S)

/-- The stabilizer group of `Q`, base-changed to `Q.U ⨯ Q.U` along the first projection. -/
def group : Grp (Over (Q.U ⨯ Q.U)) :=
  (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)).mapGrp.obj Q.stabilizer

/-- The object of `group Q` is the pullback of the stabilizer along the first projection. -/
theorem group_X :
    (group Q).X =
      (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)).obj Q.stabilizer.X := rfl

/-- The pulled-back stabilizer component and the arrow component have the same target. -/
theorem toTargetProduct_condition :
    ((fst (group Q).X Q.toPreRelation).left ≫
        pullback.fst Q.stabilizer.X.hom (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)) ≫
          Q.stabilizer.X.hom =
      (snd (group Q).X Q.toPreRelation).left ≫ Q.t := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = pullback.snd _ _ ≫ Q.t
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (pullback.fst (pullback.snd Q.stabilizer.X.hom prod.fst)
    (prod.lift Q.t Q.s) ≫ pullback.snd Q.stabilizer.X.hom prod.fst) ≫ prod.fst = _
  rw [pullback.condition, Category.assoc, prod.lift_fst]
  rfl

/-- The canonical map from the pulled-back action product to the stabilizer action product. -/
def toTargetProduct :
    ((group Q).X ⊗ Q.toPreRelation).left ⟶
      (Q.stabilizer.X ⊗ Q.arrowsOverTarget).left :=
  pullback.lift
    ((fst (group Q).X Q.toPreRelation).left ≫
      pullback.fst Q.stabilizer.X.hom (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))
    (snd (group Q).X Q.toPreRelation).left (toTargetProduct_condition Q)

/-- The first projection of `toTargetProduct Q` is the pulled-back stabilizer element. -/
theorem toTargetProduct_fst :
    toTargetProduct Q ≫ pullback.fst Q.stabilizer.X.hom Q.t =
      (fst (group Q).X Q.toPreRelation).left ≫
        pullback.fst Q.stabilizer.X.hom (prod.fst : Q.U ⨯ Q.U ⟶ Q.U) := by
  exact pullback.lift_fst _ _ _

/-- The second projection of `toTargetProduct Q` is the arrow being acted upon. -/
theorem toTargetProduct_snd :
    toTargetProduct Q ≫ pullback.snd Q.stabilizer.X.hom Q.t =
      (snd (group Q).X Q.toPreRelation).left := by
  exact pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Composition with the pulled-back stabilizer preserves the target-source pair. -/
theorem hom_condition :
    (toTargetProduct Q ≫ (actionHom Q).left) ≫ Q.toPreRelation.hom =
      ((group Q).X ⊗ Q.toPreRelation).hom := by
  apply prod.hom_ext
  · change ((toTargetProduct Q ≫ (actionHom Q).left) ≫ Q.toPreRelation.hom) ≫
        prod.fst = ((group Q).X ⊗ Q.toPreRelation).hom ≫ prod.fst
    change ((toTargetProduct Q ≫ (actionHom Q).left) ≫ prod.lift Q.t Q.s) ≫
        prod.fst = _
    simp only [Category.assoc, prod.lift_fst]
    rw [show (actionHom Q).left ≫ Q.t =
      (Q.stabilizer.X ⊗ Q.arrowsOverTarget).hom from Over.w (actionHom Q)]
    change toTargetProduct Q ≫
      (pullback.fst Q.stabilizer.X.hom Q.t ≫ Q.stabilizer.X.hom) = _
    rw [← Category.assoc, toTargetProduct_fst Q, toTargetProduct_condition Q]
    have h := congrArg (fun f => f ≫ prod.fst)
      (Over.w (snd (group Q).X Q.toPreRelation))
    simpa only [Category.assoc,
      show Q.toPreRelation.hom ≫ prod.fst = Q.t from prod.lift_fst Q.t Q.s] using h
  · change ((toTargetProduct Q ≫ (actionHom Q).left) ≫ Q.toPreRelation.hom) ≫
        prod.snd = ((group Q).X ⊗ Q.toPreRelation).hom ≫ prod.snd
    change ((toTargetProduct Q ≫ (actionPair Q ≫ Q.c)) ≫
        prod.lift Q.t Q.s) ≫ prod.snd = _
    simp only [Category.assoc, prod.lift_snd, Q.comp_source]
    simp only [actionPair, pullback.lift_snd_assoc, actionSecond]
    change toTargetProduct Q ≫ pullback.snd Q.stabilizer.X.hom Q.t ≫ Q.s = _
    rw [← Category.assoc, toTargetProduct_snd]
    have h := congrArg (fun f => f ≫ prod.snd)
      (Over.w (snd (group Q).X Q.toPreRelation))
    simpa only [Category.assoc,
      show Q.toPreRelation.hom ≫ prod.snd = Q.s from prod.lift_snd Q.t Q.s] using h

/-- The action morphism over `Q.U ⨯ Q.U` induced by groupoid composition. -/
def hom : (group Q).X ⊗ Q.toPreRelation ⟶ Q.toPreRelation :=
  Over.homMk (toTargetProduct Q ≫ (actionHom Q).left) (hom_condition Q)

/-- The underlying morphism of `hom Q` is induced by `actionHom Q`. -/
theorem hom_left :
    (hom Q).left = toTargetProduct Q ≫ (actionHom Q).left := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem groupOne_fst :
    η[(group Q).X].left ≫
      pullback.fst Q.stabilizer.X.hom (prod.fst : Q.U ⨯ Q.U ⟶ Q.U) =
    (prod.fst : Q.U ⨯ Q.U ⟶ Q.U) ≫ η[Q.stabilizer.X].left := by
  change (Functor.LaxMonoidal.ε (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)) ≫
      (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)).map η[Q.stabilizer.X]).left ≫ _ = _
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc]
  congr 1
  have hε := Over.w (Functor.LaxMonoidal.ε
    (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)))
  change (Functor.LaxMonoidal.ε (Over.pullback
    (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))).left ≫
      pullback.snd (𝟙 Q.U) prod.fst = 𝟙 (Q.U ⨯ Q.U) at hε
  calc
    _ = (Functor.LaxMonoidal.ε (Over.pullback
        (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))).left ≫
          (pullback.fst (𝟙 Q.U) prod.fst ≫ 𝟙 Q.U) := by simp
    _ = _ := by
      rw [pullback.condition, ← Category.assoc, hε]
      exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stabilizerOne_arrow :
    η[Q.stabilizer.X].left ≫ Q.toPreRelation.stabilizerToArrows = Q.e := by
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The induced action satisfies the identity-action law. -/
theorem one_smul :
    η[(group Q).X] ⊵ₗ Q.toPreRelation ≫ hom Q =
      (λₗ Q.toPreRelation).hom := by
  apply Over.OverMorphism.ext
  let r := (snd (𝟙_ (Over (Q.U ⨯ Q.U))) Q.toPreRelation).left
  have h : ((r ≫ Q.t) ≫ Q.e) ≫ Q.s = r ≫ Q.t := by
    simp [Category.assoc, Q.identity_source]
  have hr : (fst (𝟙_ (Over (Q.U ⨯ Q.U))) Q.toPreRelation).left ≫
      (prod.fst : Q.U ⨯ Q.U ⟶ Q.U) = r ≫ Q.t := by
    have hc := congrArg (fun f => f ≫ (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))
      (Over.w (snd (𝟙_ (Over (Q.U ⨯ Q.U))) Q.toPreRelation))
    simpa [r, GroupoidScheme.toPreRelation, Scheme.PreRelation.ofHom,
      Category.assoc, Over.tensorObj_hom] using hc.symm
  have hp : (η[(group Q).X] ▷ Q.toPreRelation).left ≫
      toTargetProduct Q ≫ actionPair Q = pullback.lift ((r ≫ Q.t) ≫ Q.e) r h := by
    apply pullback.hom_ext
    · simp only [Category.assoc, actionPair, pullback.lift_fst, pullback.lift_fst_assoc, actionFirst,
        toTargetProduct, Over.fst_left, Over.whiskerRight_left_fst_assoc,
        groupOne_fst_assoc, stabilizerOne_arrow]
      simpa only [← Category.assoc, Over.fst_left] using congrArg (fun f => f ≫ Q.e) hr
    · simp [Category.assoc, actionPair, actionSecond, toTargetProduct, r]
  change (η[(group Q).X] ▷ Q.toPreRelation).left ≫
    (toTargetProduct Q ≫ (actionPair Q ≫ Q.c)) = r
  calc
    _ = ((η[(group Q).X] ▷ Q.toPreRelation).left ≫
        toTargetProduct Q ≫ actionPair Q) ≫ Q.c := by simp [Category.assoc]
    _ = _ := (congrArg (fun f => f ≫ Q.c) hp).trans (Q.left_identity r h)

set_option backward.isDefEq.respectTransparency false in
private theorem hom_on_points {Z : Over (Q.U ⨯ Q.U)}
    (g : Z ⟶ (group Q).X) (x : Z ⟶ Q.toPreRelation)
    (h : (g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
      Q.toPreRelation.stabilizerToArrows) ≫ Q.s = x.left ≫ Q.t) :
    (lift g x ≫ hom Q).left =
      Q.compose (g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
        Q.toPreRelation.stabilizerToArrows) x.left h := by
  change (lift g x).left ≫ (toTargetProduct Q ≫ (actionPair Q ≫ Q.c)) = _
  unfold GroupoidScheme.compose
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [Category.assoc, actionPair, actionFirst, toTargetProduct]
  · simp [Category.assoc, actionPair, actionSecond, toTargetProduct]

set_option backward.isDefEq.respectTransparency false in
private theorem stabilizer_source :
    Q.toPreRelation.stabilizerToArrows ≫ Q.s = Q.stabilizer.X.hom := by
  change pullback.fst (prod.lift Q.t Q.s) (diag Q.U) ≫ Q.s =
    pullback.snd (prod.lift Q.t Q.s) (diag Q.U)
  have h := congrArg (fun f => f ≫ (prod.snd : Q.U ⨯ Q.U ⟶ Q.U))
    (pullback.condition (f := prod.lift Q.t Q.s) (g := diag Q.U))
  simpa [Category.assoc, diag] using h

set_option backward.isDefEq.respectTransparency false in
private theorem stabilizer_target :
    Q.toPreRelation.stabilizerToArrows ≫ Q.t = Q.stabilizer.X.hom := by
  change pullback.fst (prod.lift Q.t Q.s) (diag Q.U) ≫ Q.t =
    pullback.snd (prod.lift Q.t Q.s) (diag Q.U)
  have h := congrArg (fun f => f ≫ (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))
    (pullback.condition (f := prod.lift Q.t Q.s) (g := diag Q.U))
  simpa [Category.assoc, diag] using h

set_option backward.isDefEq.respectTransparency false in
private theorem point_target {Z : Over (Q.U ⨯ Q.U)} (x : Z ⟶ Q.toPreRelation) :
    x.left ≫ Q.t = Z.hom ≫ prod.fst := by
  simpa only [Category.assoc,
    show Q.toPreRelation.hom ≫ prod.fst = Q.t from prod.lift_fst Q.t Q.s]
    using congrArg (fun f => f ≫ (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)) (Over.w x)

set_option backward.isDefEq.respectTransparency false in
private theorem point_source {Z : Over (Q.U ⨯ Q.U)} (x : Z ⟶ Q.toPreRelation) :
    x.left ≫ Q.s = Z.hom ≫ prod.snd := by
  simpa only [Category.assoc,
    show Q.toPreRelation.hom ≫ prod.snd = Q.s from prod.lift_snd Q.t Q.s]
    using congrArg (fun f => f ≫ (prod.snd : Q.U ⨯ Q.U ⟶ Q.U)) (Over.w x)

set_option backward.isDefEq.respectTransparency false in
private theorem group_point_base {Z : Over (Q.U ⨯ Q.U)} (g : Z ⟶ (group Q).X) :
    (g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst) ≫ Q.stabilizer.X.hom =
      Z.hom ≫ prod.fst := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (g.left ≫ (group Q).X.hom) ≫ prod.fst = _
  rw [Over.w]

set_option backward.isDefEq.respectTransparency false in
private theorem group_point_ext {Z : Over (Q.U ⨯ Q.U)} (g h : Z ⟶ (group Q).X)
    (he : g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
      Q.toPreRelation.stabilizerToArrows =
      h.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
        Q.toPreRelation.stabilizerToArrows) : g = h := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact he
    · exact (group_point_base Q g).trans (group_point_base Q h).symm
  · exact (Over.w g).trans (Over.w h).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stabilizerMul_arrow :
    μ[Q.stabilizer.X].left ≫ Q.toPreRelation.stabilizerToArrows =
      stabilizerComposablePair Q ≫ Q.c := by
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem groupMul_arrow
    (hc : ((fst (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows) ≫ Q.s =
      ((snd (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows) ≫ Q.t) :
    μ[(group Q).X].left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
      Q.toPreRelation.stabilizerToArrows =
    Q.compose ((fst (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows)
      ((snd (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows) hc := by
  change (Functor.LaxMonoidal.μ (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))
      Q.stabilizer.X Q.stabilizer.X ≫
      (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)).map μ[Q.stabilizer.X]).left ≫ _ = _
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
    pullback.lift_fst_assoc, stabilizerMul_arrow]
  unfold GroupoidScheme.compose
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, stabilizerComposablePair, pullback.lift_fst,
      Over.fst_left]
    simpa only [Category.assoc, group, stabilizer, Functor.mapGrp] using congrArg
      (fun f => f ≫ Q.toPreRelation.stabilizerToArrows)
      (Over.μ_pullback_left_fst_fst (f := (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))
        Q.stabilizer.X Q.stabilizer.X)
  · simp only [Category.assoc, stabilizerComposablePair, pullback.lift_snd,
      Over.snd_left]
    simpa only [Category.assoc, group, stabilizer, Functor.mapGrp] using congrArg
      (fun f => f ≫ Q.toPreRelation.stabilizerToArrows)
      (Over.μ_pullback_left_fst_snd (f := (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))
        Q.stabilizer.X Q.stabilizer.X)

set_option backward.isDefEq.respectTransparency false in
private theorem groupMul_points {Z : Over (Q.U ⨯ Q.U)}
    (g h : Z ⟶ (group Q).X)
    (hc : (g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
        Q.toPreRelation.stabilizerToArrows) ≫ Q.s =
      (h.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
        Q.toPreRelation.stabilizerToArrows) ≫ Q.t) :
    (lift g h ≫ μ[(group Q).X]).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows =
      Q.compose (g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows)
        (h.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows) hc := by
  have hc0 : ((fst (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows) ≫ Q.s =
      ((snd (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows) ≫ Q.t := by
    simpa only [Category.assoc, stabilizer_source Q, stabilizer_target Q] using
      (group_point_base Q (fst (group Q).X (group Q).X)).trans
        (group_point_base Q (snd (group Q).X (group Q).X)).symm
  have H := congrArg (fun f => (lift g h).left ≫ f) (groupMul_arrow Q hc0)
  calc
    _ = (lift g h).left ≫ Q.compose
      ((fst (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows)
      ((snd (group Q).X (group Q).X).left ≫
        pullback.fst Q.stabilizer.X.hom prod.fst ≫
          Q.toPreRelation.stabilizerToArrows) hc0 := by
      simpa only [Over.comp_left, Category.assoc] using H
    _ = _ := by
      unfold GroupoidScheme.compose
      rw [← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · simp [Category.assoc]
      · simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem mul_action_points {Z : Over (Q.U ⨯ Q.U)}
    (g h : Z ⟶ (group Q).X) (x : Z ⟶ Q.toPreRelation) :
    lift (lift g h ≫ μ[(group Q).X]) x ≫ hom Q =
      lift g (lift h x ≫ hom Q) ≫ hom Q := by
  let a := g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
    Q.toPreRelation.stabilizerToArrows
  let b := h.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
    Q.toPreRelation.stabilizerToArrows
  have hs (g' : Z ⟶ (group Q).X) :
      (g'.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
        Q.toPreRelation.stabilizerToArrows) ≫ Q.s = Z.hom ≫ prod.fst := by
    simpa only [Category.assoc, stabilizer_source Q] using group_point_base Q g'
  have ht (g' : Z ⟶ (group Q).X) :
      (g'.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
        Q.toPreRelation.stabilizerToArrows) ≫ Q.t = Z.hom ≫ prod.fst := by
    simpa only [Category.assoc, stabilizer_target Q] using group_point_base Q g'
  have hab : a ≫ Q.s = b ≫ Q.t := (hs g).trans (ht h).symm
  have hbx : b ≫ Q.s = x.left ≫ Q.t := (hs h).trans (point_target Q x).symm
  have habx : Q.compose a b hab ≫ Q.s = x.left ≫ Q.t := by
    simpa [GroupoidScheme.compose, Category.assoc, Q.comp_source] using hbx
  have haxb : a ≫ Q.s = Q.compose b x.left hbx ≫ Q.t := by
    simpa [GroupoidScheme.compose, Category.assoc, Q.comp_target] using hab
  have hmul := groupMul_points Q g h hab
  have hx := hom_on_points Q h x hbx
  have hL := hom_on_points Q (lift g h ≫ μ[(group Q).X]) x
    ((hs _).trans (point_target Q x).symm)
  have hR := hom_on_points Q g (lift h x ≫ hom Q)
    ((hs _).trans (point_target Q _).symm)
  have hL' : (lift (lift g h ≫ μ[(group Q).X]) x ≫ hom Q).left =
      Q.compose (Q.compose a b hab) x.left habx := by
    simpa only [hmul] using hL
  have hR' : (lift g (lift h x ≫ hom Q) ≫ hom Q).left =
      Q.compose a (Q.compose b x.left hbx) haxb := by
    simpa only [hx] using hR
  apply Over.OverMorphism.ext
  exact hL'.trans ((Q.associativity a b x.left hab hbx habx haxb).trans hR'.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The induced action is compatible with multiplication in `group Q`. -/
theorem mul_smul :
    μ[(group Q).X] ⊵ₗ Q.toPreRelation ≫ hom Q =
      (αₗ (group Q).X (group Q).X Q.toPreRelation).hom ≫
        (group Q).X ⊴ₗ hom Q ≫ hom Q := by
  change (μ[(group Q).X] ▷ Q.toPreRelation) ≫ hom Q =
    (α_ (group Q).X (group Q).X Q.toPreRelation).hom ≫
      ((group Q).X ◁ hom Q) ≫ hom Q
  let Z := ((group Q).X ⊗ (group Q).X) ⊗ Q.toPreRelation
  let g : Z ⟶ (group Q).X :=
    fst _ _ ≫ fst _ _
  let h : Z ⟶ (group Q).X :=
    fst _ _ ≫ snd _ _
  let x : Z ⟶ Q.toPreRelation := snd _ _
  have hp : lift (lift g h) x = 𝟙 Z := by
    simp only [g, h, x, lift_comp_fst_snd, lift_fst_snd]
    rfl
  have H : lift (lift g h) x ≫ (μ[(group Q).X] ▷ Q.toPreRelation) ≫ hom Q =
      lift (lift g h) x ≫ (α_ (group Q).X (group Q).X Q.toPreRelation).hom ≫
        ((group Q).X ◁ hom Q) ≫ hom Q := by
    simpa only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc,
      lift_whiskerLeft_assoc] using mul_action_points Q g h x
  simpa only [hp, Category.id_comp, Z] using H

/-- The module-object structure on the arrow scheme over `Q.U ⨯ Q.U`. -/
@[reducible]
def modObj : ModObj (group Q).X Q.toPreRelation where
  smul := hom Q
  one_smul := one_smul Q
  mul_smul := mul_smul Q

/-- The action of the base-changed stabilizer on the arrow scheme over `Q.U ⨯ Q.U`. -/
def action : Mod (Over (Q.U ⨯ Q.U)) (group Q).X where
  X := Q.toPreRelation
  mod := modObj Q

/-- The object acted on by `action Q` is exactly the arrow scheme over `Q.U ⨯ Q.U`. -/
theorem action_X :
    (action Q).X = Q.toPreRelation := rfl

/-- The action morphism stored by `action Q` is `hom Q`. -/
theorem action_smul :
    (action Q).mod.smul = hom Q := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem compose_cancel_inv {T : Over S} (a b : T ⟶ Q.R)
    (h : a ≫ Q.s = b ≫ Q.t) :
    Q.compose (Q.compose a b h) (b ≫ Q.i)
      (by simp [GroupoidScheme.compose, Category.assoc, Q.comp_source, Q.inverse_target]) = a := by
  unfold GroupoidScheme.compose
  rw [Q.associativity a b (b ≫ Q.i) h
    (by simp [Category.assoc, Q.inverse_target]) _
    (by simpa [Category.assoc, Q.comp_target] using h)]
  trans pullback.lift a ((a ≫ Q.s) ≫ Q.e)
    (by simp [Category.assoc, Q.identity_target]) ≫ Q.c
  · congr 1
    apply pullback.hom_ext
    · simp
    · simp only [pullback.lift_snd]
      exact (Q.inverse_comp b _).trans (congrArg (fun f => f ≫ Q.e) h.symm)
  · exact Q.right_identity a _

set_option backward.isDefEq.respectTransparency false in
private theorem compose_inv_cancel {T : Over S} (a b : T ⟶ Q.R)
    (h : a ≫ Q.s = b ≫ Q.s) :
    Q.compose (Q.compose a (b ≫ Q.i) (by simpa [Category.assoc, Q.inverse_target] using h)) b
      (by simp [GroupoidScheme.compose, Category.assoc, Q.comp_source, Q.inverse_source]) = a := by
  unfold GroupoidScheme.compose
  rw [Q.associativity a (b ≫ Q.i) b
    (by simpa [Category.assoc, Q.inverse_target] using h)
    (by simp [Category.assoc, Q.inverse_source]) _
    (by simpa [Category.assoc, Q.comp_target, Q.inverse_target] using h)]
  trans pullback.lift a ((a ≫ Q.s) ≫ Q.e)
    (by simp [Category.assoc, Q.identity_target]) ≫ Q.c
  · congr 1
    apply pullback.hom_ext
    · simp
    · simp only [pullback.lift_snd]
      exact (Q.comp_inverse b _).trans (congrArg (fun f => f ≫ Q.e) h.symm)
  · exact Q.right_identity a _

set_option backward.isDefEq.respectTransparency false in
/-- The relation of a groupoid scheme is a pseudo-torsor under its base-changed stabilizer. -/
theorem isPseudoTorsor : Mod.IsPseudoTorsor (action Q) := by
  letI := modObj Q
  constructor
  apply ModObj.isIso_leftSMul_iff.mpr
  intro Z x y
  have hxy : y.left ≫ Q.s = x.left ≫ Q.s :=
    (point_source Q y).trans (point_source Q x).symm
  let k := Q.compose y.left (x.left ≫ Q.i)
    (by simpa [Category.assoc, Q.inverse_target] using hxy)
  have kt : k ≫ Q.t = Z.hom ≫ prod.fst := by
    simpa [k, GroupoidScheme.compose, Category.assoc, Q.comp_target]
      using point_target Q y
  have ks : k ≫ Q.s = Z.hom ≫ prod.fst := by
    simpa [k, GroupoidScheme.compose, Category.assoc, Q.comp_source, Q.inverse_source]
      using point_target Q x
  have hk : k ≫ Q.toPreRelation.hom = (Z.hom ≫ prod.fst) ≫ diag Q.U := by
    apply prod.hom_ext
    · simpa [Category.assoc, GroupoidScheme.toPreRelation, Scheme.PreRelation.ofHom, diag]
        using kt
    · simpa [Category.assoc, GroupoidScheme.toPreRelation, Scheme.PreRelation.ofHom, diag]
        using ks
  let gs : Z.left ⟶ Q.stabilizer.X.left :=
    pullback.lift k (Z.hom ≫ prod.fst) hk
  let g : Z ⟶ (group Q).X := Over.homMk
    (pullback.lift gs Z.hom (show gs ≫ Q.stabilizer.X.hom = Z.hom ≫ prod.fst from
      pullback.lift_snd _ _ _)) (pullback.lift_snd _ _ _)
  have hg : g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
      Q.toPreRelation.stabilizerToArrows = k := by
    simp [g, gs, Scheme.PreRelation.stabilizerToArrows]
  refine ⟨g, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (lift g x ≫ hom Q).left = y.left
    have hcomp : (g.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
        Q.toPreRelation.stabilizerToArrows) ≫ Q.s = x.left ≫ Q.t := by
      exact (congrArg (fun f => f ≫ Q.s) hg).trans
        (ks.trans (point_target Q x).symm)
    have hm := hom_on_points Q g x hcomp
    have hm' : (lift g x ≫ hom Q).left =
        Q.compose k x.left (ks.trans (point_target Q x).symm) := by
      simpa only [hg] using hm
    exact hm'.trans (compose_inv_cancel Q y.left x.left hxy)
  · intro g' hh
    let a := g'.left ≫ pullback.fst Q.stabilizer.X.hom prod.fst ≫
      Q.toPreRelation.stabilizerToArrows
    have ha : a ≫ Q.s = x.left ≫ Q.t := by
      simp only [a, Category.assoc, stabilizer_source Q]
      exact ((Category.assoc _ _ _).symm.trans (group_point_base Q g')).trans
        (point_target Q x).symm
    have hh' : Q.compose a x.left ha = y.left := by
      change lift g' x ≫ hom Q = y at hh
      exact (hom_on_points Q g' x ha).symm.trans (congrArg Over.Hom.left hh)
    have he : a = k := by
      calc
        a = Q.compose (Q.compose a x.left ha) (x.left ≫ Q.i) _ :=
          (compose_cancel_inv Q a x.left ha).symm
        _ = k := by
          change pullback.lift (Q.compose a x.left ha) (x.left ≫ Q.i) _ ≫ Q.c =
            pullback.lift y.left (x.left ≫ Q.i) _ ≫ Q.c
          congr 1
          apply pullback.hom_ext
          · simpa only [pullback.lift_fst] using hh'
          · simp
    exact group_point_ext Q g' g (he.trans hg.symm)

end AlgebraicGeometry.GroupoidScheme.RelationAction
