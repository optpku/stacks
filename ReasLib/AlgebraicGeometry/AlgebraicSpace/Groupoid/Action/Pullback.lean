/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InvariantBaseChange

/-!
# Pullback of invariant actions of group algebraic spaces

An invariant morphism from a space with a group action induces an action on each
fibre product over its target. The associated action pre-relation is canonically
isomorphic to the invariant base change of the original action pre-relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ModObj
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

open AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The two projections of the induced action on `U' = pullback φ f` form a cone over
`φ` and `f`. -/
private theorem smulPullback_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    ((G.X ◁ Limits.pullback.fst φ f) ≫ γ[G.X, Xg.X]) ≫ φ =
      (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f) ≫ f := sorry

/-- The action map of the induced `G`-action on `U' = pullback φ f`. -/
def smulPullback {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    G.X ⊗ Limits.pullback φ f ⟶ Limits.pullback φ f :=
  Limits.pullback.lift ((G.X ◁ Limits.pullback.fst φ f) ≫ γ[G.X, Xg.X])
    (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f)
    (by exact smulPullback_condition G Xg φ hφ f)

/-- The induced `G`-action on `U' = pullback φ f` along an invariant morphism `φ`. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    Action G where
  X := Limits.pullback φ f
  mod :=
    { smul := smulPullback G Xg φ hφ f
      one_smul := sorry
      mul_smul := sorry }

/-- The underlying object of the induced action is `U' = pullback φ f`. -/
theorem pullback_X {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (pullback G Xg φ hφ f).X = Limits.pullback φ f := sorry

/-- The action map of the induced action is `smulPullback`. -/
theorem pullback_smul {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    γ[G.X, (pullback G Xg φ hφ f).X] = smulPullback G Xg φ hφ f := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Invariance makes `(g, u') ↦ (g, u)` a cone over `t ≫ φ` and `f`. -/
private theorem actionPullbackArrowHom_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (G.X ◁ Limits.pullback.fst φ f) ≫ ((ofAction G Xg).toPreRelation.t ≫ φ) =
      (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f) ≫ f := sorry

/-- The canonical map `G.X ⊗ pullback φ f ⟶ pullback (t ≫ φ) f` induced by
invariance. -/
def actionPullbackArrowHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    G.X ⊗ Limits.pullback φ f ⟶
      pullback ((ofAction G Xg).toPreRelation.t ≫ φ) f :=
  Limits.pullback.lift (G.X ◁ Limits.pullback.fst φ f)
    (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f)
    (by exact actionPullbackArrowHom_w G Xg φ hφ f)

/-- The pair `(g, u)` and the `X'`-coordinate of `X' ×_X (G ⊗ U)` form a cone over
`φ` and `f`. -/
private theorem actionPullbackArrowInv_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (Limits.pullback.fst ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫
        snd G.X Xg.X) ≫ φ =
      Limits.pullback.snd ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫ f := sorry

/-- Inverse of `actionPullbackArrowHom`, pairing the group coordinate with the
induced point of `U'`. -/
def actionPullbackArrowInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    pullback ((ofAction G Xg).toPreRelation.t ≫ φ) f ⟶
      G.X ⊗ Limits.pullback φ f :=
  CartesianMonoidalCategory.lift
    (Limits.pullback.fst ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫ fst G.X Xg.X)
    (Limits.pullback.lift
      (Limits.pullback.fst ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫ snd G.X Xg.X)
      (Limits.pullback.snd ((ofAction G Xg).toPreRelation.t ≫ φ) f)
      (by exact actionPullbackArrowInv_w G Xg φ hφ f))

/-- Canonical isomorphism `G.X ⊗ U' ≅ X' ×_X (G ⊗ U)` induced by invariance of
`φ`, as an identification of chosen fibre products in `Over B`. -/
def actionPullbackArrowIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    G.X ⊗ Limits.pullback φ f ≅
      pullback ((ofAction G Xg).toPreRelation.t ≫ φ) f :=
  { hom := actionPullbackArrowHom G Xg φ hφ f
    inv := actionPullbackArrowInv G Xg φ hφ f
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Triangle witnessing that `actionPullbackArrowIso` identifies the induced-action
pre-relation with the invariant base change. -/
private theorem toPreRelation_pullback_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (actionPullbackArrowIso G Xg φ hφ f).hom ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).hom =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.hom := sorry

/-- The underlying pre-relation of the induced `G`-action on `U'` is canonically
isomorphic to the invariant base change of the original action groupoid. -/
def toPreRelation_pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation ≅
      (ofAction G Xg).toPreRelation.baseChange hφ f :=
  Over.isoMk (actionPullbackArrowIso G Xg φ hφ f)
    (by exact toPreRelation_pullback_w G Xg φ hφ f)

/-- The action comparison identifies defining maps of the two pre-relations. -/
theorem toPreRelation_pullback_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (toPreRelation_pullback G Xg φ hφ f).hom.left ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).hom =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.hom := sorry

/-- The action comparison identifies target projections of the two pre-relations. -/
theorem toPreRelation_pullback_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (toPreRelation_pullback G Xg φ hφ f).hom.left ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).t =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.t := sorry

/-- The action comparison identifies source projections of the two pre-relations. -/
theorem toPreRelation_pullback_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (toPreRelation_pullback G Xg φ hφ f).hom.left ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).s =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.s := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
