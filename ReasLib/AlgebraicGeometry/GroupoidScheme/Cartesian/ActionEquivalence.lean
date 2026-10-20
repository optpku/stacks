/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action.Category
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.CartesianOver

/-!
# Comparison between cartesian groupoid schemes and actions

This module supplies the concrete equivalence between cartesian groupoid schemes over a fixed
groupoid scheme and schemes over the object scheme equipped with a compatible action.
-/

/-- The source square of a cartesian groupoid-scheme morphism is cartesian on underlying
schemes. -/
theorem sourceSquare {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    IsPullback Z.obj.left.s.left Z.obj.hom.arrow.left Z.obj.hom.obj.left G.s.left := by
  exact ((GroupoidScheme.Hom.isCartesian_iff Z.obj.hom).1 Z.property).flip

/-- The arrow scheme of a cartesian groupoid scheme is the source pullback on the level of
objects over `S`. -/
noncomputable def arrowToSourceLeftIso {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Z.obj.left.R ≅ ((Over.pullback G.s).obj (Over.mk Z.obj.hom.obj)).left :=
  Over.isoMk
    ((sourceSquare Z).isoPullback ≪≫
      (CategoryTheory.Limits.PreservesPullback.iso
        (Over.forget S) Z.obj.hom.obj G.s).symm)
    (by sorry)

/-- The arrow scheme of a cartesian groupoid scheme is the source pullback. -/
noncomputable def arrowToSource {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Over.mk Z.obj.hom.arrow ≅
      (Over.pullback G.s).obj (Over.mk Z.obj.hom.obj) :=
  Over.isoMk (arrowToSourceLeftIso Z) (by sorry)

/-- The lifted inverse arrow above a target pullback point. -/
noncomputable def toActionHomLift {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    ((Over.pullback G.t).obj (Over.mk Z.obj.hom.obj)).left ⟶ Z.obj.left.R :=
  Over.homMk
    ((sourceSquare Z).lift
      (Limits.pullback.fst Z.obj.hom.obj G.t).left
      ((Limits.pullback.snd Z.obj.hom.obj G.t ≫ G.i).left)
      (by sorry))
    (by sorry)

/-- The underlying map from the target pullback to the source pullback induced by a cartesian
groupoid scheme. -/
noncomputable def toActionHomLeft {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    ((Over.pullback G.t).obj (Over.mk Z.obj.hom.obj)).left ⟶
      ((Over.pullback G.s).obj (Over.mk Z.obj.hom.obj)).left :=
  Limits.pullback.lift
    (toActionHomLift Z ≫ Z.obj.left.t)
    ((Over.pullback G.t).obj (Over.mk Z.obj.hom.obj)).hom
    (by sorry)

/-- The lifted arrow above a source pullback point. -/
noncomputable def toActionInvLift {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    ((Over.pullback G.s).obj (Over.mk Z.obj.hom.obj)).left ⟶ Z.obj.left.R :=
  Over.homMk
    ((sourceSquare Z).lift
      (Limits.pullback.fst Z.obj.hom.obj G.s).left
      (Limits.pullback.snd Z.obj.hom.obj G.s).left
      (by sorry))
    (by sorry)

/-- The underlying map from the source pullback to the target pullback induced by a cartesian
groupoid scheme. -/
noncomputable def toActionInvLeft {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    ((Over.pullback G.s).obj (Over.mk Z.obj.hom.obj)).left ⟶
      ((Over.pullback G.t).obj (Over.mk Z.obj.hom.obj)).left :=
  Limits.pullback.lift
    (toActionInvLift Z ≫ Z.obj.left.t)
    ((Over.pullback G.s).obj (Over.mk Z.obj.hom.obj)).hom
    (by sorry)

/-- The action isomorphism induced by a cartesian groupoid-scheme morphism. -/
noncomputable def toActionIso {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    (Over.pullback G.t).obj (Over.mk Z.obj.hom.obj) ≅
      (Over.pullback G.s).obj (Over.mk Z.obj.hom.obj) :=
  { hom := Over.homMk (toActionHomLeft Z) (by sorry)
    inv := Over.homMk (toActionInvLeft Z) (by sorry)
    hom_inv_id := by sorry
    inv_hom_id := by sorry }

/-- The arrow scheme of a cartesian groupoid scheme is the target pullback. -/
noncomputable def arrowToTarget {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Over.mk Z.obj.hom.arrow ≅
      (Over.pullback G.t).obj (Over.mk Z.obj.hom.obj) :=
  arrowToSource Z ≪≫ (toActionIso Z).symm

/-- The induced action isomorphism satisfies the unit law. -/
theorem toActionIso_unit {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    GroupoidScheme.Action.IsUnital G (Over.mk Z.obj.hom.obj) (toActionIso Z) := sorry

/-- The induced action isomorphism satisfies the cocycle law. -/
theorem toActionIso_cocycle {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    GroupoidScheme.Action.IsCocycle G (Over.mk Z.obj.hom.obj) (toActionIso Z) := sorry

/-- A cartesian groupoid scheme determines its explicit groupoid action. -/
noncomputable def toActionObj {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) : GroupoidScheme.Action G :=
  GroupoidScheme.Action.ofIso G (Over.mk Z.obj.hom.obj) (toActionIso Z)
    (toActionIso_unit Z) (toActionIso_cocycle Z)

/-- The object map of a morphism of cartesian groupoid schemes lies over `G.U`. -/
theorem toActionMap_w {S : Scheme.{u}} {G : GroupoidScheme S}
    {Z W : GroupoidScheme.CartesianOver G} (a : Z ⟶ W) :
    a.hom.left.obj ≫ W.obj.hom.obj = Z.obj.hom.obj := sorry

/-- The object map underlying the induced morphism of actions. -/
def toActionMapUnderlying {S : Scheme.{u}} {G : GroupoidScheme S}
    {Z W : GroupoidScheme.CartesianOver G} (a : Z ⟶ W) :
    Over.mk Z.obj.hom.obj ⟶ Over.mk W.obj.hom.obj :=
  Over.homMk a.hom.left.obj (toActionMap_w a)

/-- The induced object map forms the canonical commutative square with the action
isomorphisms. -/
theorem toActionMap_compatibility {S : Scheme.{u}} {G : GroupoidScheme S}
    {Z W : GroupoidScheme.CartesianOver G} (a : Z ⟶ W) :
    CommSq (toActionIso Z).hom ((Over.pullback G.t).map (toActionMapUnderlying a))
      ((Over.pullback G.s).map (toActionMapUnderlying a)) (toActionIso W).hom := sorry

/-- A morphism of cartesian groupoid schemes induces a morphism of actions. -/
noncomputable def toActionMap {S : Scheme.{u}} {G : GroupoidScheme S}
    {Z W : GroupoidScheme.CartesianOver G} (a : Z ⟶ W) :
    toActionObj Z ⟶ toActionObj W :=
  GroupoidScheme.Action.System.Hom.ofMap (toActionMapUnderlying a)
    (toActionMap_compatibility a)

/-- The action construction preserves identity morphisms. -/
theorem toActionMap_id {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    toActionMap (𝟙 Z) = 𝟙 (toActionObj Z) := sorry

/-- The action construction preserves composition. -/
theorem toActionMap_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    {Z W Q : GroupoidScheme.CartesianOver G} (a : Z ⟶ W) (b : W ⟶ Q) :
    toActionMap (a ≫ b) = toActionMap a ≫ toActionMap b := sorry

/-- The concrete functor from cartesian groupoid schemes to groupoid actions. -/
noncomputable def toAction {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidScheme.CartesianOver G ⥤ GroupoidScheme.Action G where
  obj := toActionObj
  map := toActionMap
  map_id := toActionMap_id
  map_comp := toActionMap_comp

/-- The object of `Over S` underlying the arrow scheme of the transformation groupoid. -/
noncomputable abbrev actionArrowObj {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : Over S :=
  ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left

/-- The arrow projection of the action groupoid. -/
noncomputable def actionArrow {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left ⟶ G.R :=
  Limits.pullback.snd (GroupoidScheme.Action.obj A).hom G.t

/-- The target map of the action groupoid. -/
noncomputable def actionTarget {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left ⟶
      (GroupoidScheme.Action.obj A).left :=
  Limits.pullback.fst (GroupoidScheme.Action.obj A).hom G.t

/-- The source map of the action groupoid. -/
noncomputable def actionSource {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left ⟶
      (GroupoidScheme.Action.obj A).left :=
  (GroupoidScheme.Action.iso A).hom.left ≫
    Limits.pullback.fst (GroupoidScheme.Action.obj A).hom G.s

/-- The identity-arrow lift satisfies the target-pullback equation. -/
theorem actionIdentity_condition {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    𝟙 (GroupoidScheme.Action.obj A).left ≫ (GroupoidScheme.Action.obj A).hom =
      ((GroupoidScheme.Action.obj A).hom ≫ G.e) ≫ G.t := sorry

/-- The identity-arrow map of the action groupoid. -/
noncomputable def actionIdentity {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    (GroupoidScheme.Action.obj A).left ⟶
      ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left :=
  Limits.pullback.lift (𝟙 _) ((GroupoidScheme.Action.obj A).hom ≫ G.e)
    (actionIdentity_condition A)

/-- The inverse-arrow lift satisfies the target-pullback equation. -/
theorem actionInverse_condition {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    actionSource A ≫ (GroupoidScheme.Action.obj A).hom =
      (actionArrow A ≫ G.i) ≫ G.t := sorry

/-- The inverse-arrow map of the action groupoid. -/
noncomputable def actionInverse {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left ⟶
      ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left :=
  Limits.pullback.lift (actionSource A) (actionArrow A ≫ G.i)
    (actionInverse_condition A)

/-- The two projected arrows of a composable action-groupoid pair are composable in `G`. -/
theorem actionCompositeArrow_condition {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    (Limits.pullback.fst (actionSource A) (actionTarget A) ≫ actionArrow A) ≫ G.s =
      (Limits.pullback.snd (actionSource A) (actionTarget A) ≫ actionArrow A) ≫ G.t := sorry

/-- The arrow of `G` underlying a composite action-groupoid arrow. -/
noncomputable def actionCompositeArrow {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    Limits.pullback (actionSource A) (actionTarget A) ⟶ G.R :=
  Limits.pullback.lift
      (Limits.pullback.fst (actionSource A) (actionTarget A) ≫ actionArrow A)
      (Limits.pullback.snd (actionSource A) (actionTarget A) ≫ actionArrow A)
      (actionCompositeArrow_condition A) ≫ G.c

/-- The composite action arrow satisfies the target-pullback equation. -/
theorem actionComposition_condition {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    (Limits.pullback.fst (actionSource A) (actionTarget A) ≫ actionTarget A) ≫
        (GroupoidScheme.Action.obj A).hom =
      actionCompositeArrow A ≫ G.t := sorry

/-- Composition in the action groupoid. -/
noncomputable def actionComposition {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    Limits.pullback (actionSource A) (actionTarget A) ⟶
      ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left :=
  Limits.pullback.lift
    (Limits.pullback.fst (actionSource A) (actionTarget A) ≫ actionTarget A)
    (actionCompositeArrow A) (actionComposition_condition A)

/-- The action-groupoid composition has the expected source. -/
theorem actionComposition_source {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    actionComposition A ≫ actionSource A =
      Limits.pullback.snd (actionSource A) (actionTarget A) ≫ actionSource A := sorry

/-- The action-groupoid composition has the expected target. -/
theorem actionComposition_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    actionComposition A ≫ actionTarget A =
      Limits.pullback.fst (actionSource A) (actionTarget A) ≫ actionTarget A := sorry

/-- The action-groupoid identity has the expected source. -/
theorem actionIdentity_source {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : actionIdentity A ≫ actionSource A = 𝟙 _ := sorry

/-- The action-groupoid identity has the expected target. -/
theorem actionIdentity_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : actionIdentity A ≫ actionTarget A = 𝟙 _ := sorry

/-- Action-groupoid inversion exchanges source and target. -/
theorem actionInverse_source {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : actionInverse A ≫ actionSource A = actionTarget A := sorry

/-- Action-groupoid inversion exchanges target and source. -/
theorem actionInverse_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : actionInverse A ≫ actionTarget A = actionSource A := sorry

/-- Composition in the action groupoid is associative. -/
theorem actionComposition_assoc {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) {T : Over S}
    (a b d : T ⟶ ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left)
    (h_ab : a ≫ actionSource A = b ≫ actionTarget A)
    (h_bd : b ≫ actionSource A = d ≫ actionTarget A)
    (h_ab_d : (Limits.pullback.lift a b h_ab ≫ actionComposition A) ≫ actionSource A =
      d ≫ actionTarget A)
    (h_a_bd : a ≫ actionSource A =
      (Limits.pullback.lift b d h_bd ≫ actionComposition A) ≫ actionTarget A) :
    Limits.pullback.lift (Limits.pullback.lift a b h_ab ≫ actionComposition A) d h_ab_d ≫
        actionComposition A =
      Limits.pullback.lift a
          (Limits.pullback.lift b d h_bd ≫ actionComposition A) h_a_bd ≫
        actionComposition A := sorry

/-- The action-groupoid identity is a right identity. -/
theorem actionComposition_rightIdentity {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) {T : Over S}
    (a : T ⟶ ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left)
    (h : a ≫ actionSource A = ((a ≫ actionSource A) ≫ actionIdentity A) ≫ actionTarget A) :
    Limits.pullback.lift a ((a ≫ actionSource A) ≫ actionIdentity A) h ≫
        actionComposition A =
      a := sorry

/-- The action-groupoid identity is a left identity. -/
theorem actionComposition_leftIdentity {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) {T : Over S}
    (a : T ⟶ ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left)
    (h : ((a ≫ actionTarget A) ≫ actionIdentity A) ≫ actionSource A = a ≫ actionTarget A) :
    Limits.pullback.lift ((a ≫ actionTarget A) ≫ actionIdentity A) a h ≫ actionComposition A =
      a := sorry

/-- Composing an action-groupoid arrow with its inverse gives the identity at its target. -/
theorem actionComposition_inverse {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) {T : Over S}
    (a : T ⟶ ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left)
    (h : a ≫ actionSource A = (a ≫ actionInverse A) ≫ actionTarget A) :
    Limits.pullback.lift a (a ≫ actionInverse A) h ≫ actionComposition A =
      (a ≫ actionTarget A) ≫ actionIdentity A := sorry

/-- Composing the inverse of an action-groupoid arrow with it gives the identity at its source. -/
theorem actionInverse_composition {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) {T : Over S}
    (a : T ⟶ ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left)
    (h : (a ≫ actionInverse A) ≫ actionSource A = a ≫ actionTarget A) :
    Limits.pullback.lift (a ≫ actionInverse A) a h ≫ actionComposition A =
      (a ≫ actionSource A) ≫ actionIdentity A := sorry

/-- The transformation groupoid attached to a groupoid action. -/
noncomputable def actionGroupoid {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : GroupoidScheme S where
  U := (GroupoidScheme.Action.obj A).left
  R := ((Over.pullback G.t).obj (GroupoidScheme.Action.obj A)).left
  s := actionSource A
  t := actionTarget A
  c := actionComposition A
  e := actionIdentity A
  i := actionInverse A
  comp_source := actionComposition_source A
  comp_target := actionComposition_target A
  identity_source := actionIdentity_source A
  identity_target := actionIdentity_target A
  inverse_source := actionInverse_source A
  inverse_target := actionInverse_target A
  associativity := actionComposition_assoc A
  right_identity := actionComposition_rightIdentity A
  left_identity := actionComposition_leftIdentity A
  inverse_comp := actionComposition_inverse A
  comp_inverse := actionInverse_composition A

/-- The action-groupoid source map is compatible with the action projection. -/
theorem actionGroupoidHom_map_s {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    actionSource A ≫ (GroupoidScheme.Action.obj A).hom = actionArrow A ≫ G.s := sorry

/-- The action-groupoid target map is compatible with the action projection. -/
theorem actionGroupoidHom_map_t {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    actionTarget A ≫ (GroupoidScheme.Action.obj A).hom = actionArrow A ≫ G.t := sorry

/-- The action groupoid maps to the acting groupoid. -/
noncomputable def actionGroupoidHom {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : GroupoidScheme.Hom (actionGroupoid A) G where
  obj := (GroupoidScheme.Action.obj A).hom
  arrow := actionArrow A
  map_s := actionGroupoidHom_map_s A
  map_t := actionGroupoidHom_map_t A
  map_c := by sorry

/-- The map on composable arrows induced by the projection from the action groupoid to `G`. -/
noncomputable def actionGroupoidHomComposableMap {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    Limits.pullback (actionSource A) (actionTarget A) ⟶ Limits.pullback G.s G.t :=
  (actionGroupoidHom A).composableMap

/-- The action-groupoid projection preserves composition. -/
theorem actionGroupoidHom_map_c {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    actionComposition A ≫ actionArrow A =
      actionGroupoidHomComposableMap A ≫ G.c :=
  (actionGroupoidHom A).map_c

/-- The action-groupoid projection is cartesian. -/
theorem actionGroupoidHom_isCartesian {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : (actionGroupoidHom A).IsCartesian := sorry

/-- Regard an action groupoid as a groupoid scheme cartesian over `G`. -/
noncomputable def fromActionObj {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : GroupoidScheme.CartesianOver G :=
  GroupoidScheme.CartesianOver.ofHom (actionGroupoidHom A)
    (actionGroupoidHom_isCartesian A)

/-- An action morphism respects the source map of the associated action groupoids. -/
theorem actionGroupoidMap_map_s {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    actionSource A ≫ (GroupoidScheme.Action.hom a).left =
      ((Over.pullback G.t).map (GroupoidScheme.Action.hom a)).left ≫ actionSource B := sorry

/-- An action morphism respects the target map of the associated action groupoids. -/
theorem actionGroupoidMap_map_t {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    actionTarget A ≫ (GroupoidScheme.Action.hom a).left =
      ((Over.pullback G.t).map (GroupoidScheme.Action.hom a)).left ≫ actionTarget B := sorry

/-- An action morphism induces a morphism of action groupoids. -/
noncomputable def actionGroupoidMap {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    GroupoidScheme.Hom (actionGroupoid A) (actionGroupoid B) where
  obj := (GroupoidScheme.Action.hom a).left
  arrow := ((Over.pullback G.t).map (GroupoidScheme.Action.hom a)).left
  map_s := actionGroupoidMap_map_s a
  map_t := actionGroupoidMap_map_t a
  map_c := by sorry

/-- The map on composable arrows induced by a morphism of action groupoids. -/
noncomputable def actionGroupoidMapComposableMap {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    Limits.pullback (actionSource A) (actionTarget A) ⟶
      Limits.pullback (actionSource B) (actionTarget B) :=
  (actionGroupoidMap a).composableMap

/-- A morphism between action groupoids preserves composition. -/
theorem actionGroupoidMap_map_c {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    actionComposition A ≫ ((Over.pullback G.t).map (GroupoidScheme.Action.hom a)).left =
      actionGroupoidMapComposableMap a ≫ actionComposition B :=
  (actionGroupoidMap a).map_c

/-- The induced morphism of action groupoids commutes with their projections to `G`. -/
theorem fromActionMap_w {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    GroupoidScheme.Hom.comp (actionGroupoidMap a) (actionGroupoidHom B) =
      actionGroupoidHom A := sorry

/-- A morphism of actions induces a morphism of cartesian groupoid schemes. -/
noncomputable def fromActionMap {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    fromActionObj A ⟶ fromActionObj B :=
  ObjectProperty.homMk (Over.homMk (actionGroupoidMap a) (fromActionMap_w a))

/-- The action-groupoid construction preserves identity morphisms. -/
theorem fromActionMap_id {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : fromActionMap (𝟙 A) = 𝟙 (fromActionObj A) := sorry

/-- The action-groupoid construction preserves composition. -/
theorem fromActionMap_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B C : GroupoidScheme.Action G} (a : A ⟶ B) (b : B ⟶ C) :
    fromActionMap (a ≫ b) = fromActionMap a ≫ fromActionMap b := sorry

/-- The concrete functor sending an action to its transformation groupoid. -/
noncomputable def fromAction {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidScheme.Action G ⥤ GroupoidScheme.CartesianOver G where
  obj := fromActionObj
  map := fromActionMap
  map_id := fromActionMap_id
  map_comp := fromActionMap_comp

/-- The comparison from a cartesian groupoid scheme to the groupoid reconstructed from its
action preserves source. -/
theorem cartesianRoundtripHom_map_s {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Z.obj.left.s ≫ 𝟙 Z.obj.left.U =
      (arrowToTarget Z).hom.left ≫ actionSource (toActionObj Z) := sorry

/-- The comparison from a cartesian groupoid scheme to the reconstructed groupoid preserves
target. -/
theorem cartesianRoundtripHom_map_t {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Z.obj.left.t ≫ 𝟙 Z.obj.left.U =
      (arrowToTarget Z).hom.left ≫ actionTarget (toActionObj Z) := sorry

/-- The forward comparison with the action-groupoid reconstruction. -/
noncomputable def cartesianRoundtripHom {S : Scheme.{u}}
    {G : GroupoidScheme S} (Z : GroupoidScheme.CartesianOver G) :
    GroupoidScheme.Hom Z.obj.left (actionGroupoid (toActionObj Z)) where
  obj := 𝟙 Z.obj.left.U
  arrow := (arrowToTarget Z).hom.left
  map_s := cartesianRoundtripHom_map_s Z
  map_t := cartesianRoundtripHom_map_t Z
  map_c := by sorry

/-- The map on composable arrows induced by the forward cartesian roundtrip comparison. -/
noncomputable def cartesianRoundtripHomComposableMap {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Limits.pullback Z.obj.left.s Z.obj.left.t ⟶
      Limits.pullback (actionSource (toActionObj Z)) (actionTarget (toActionObj Z)) :=
  (cartesianRoundtripHom Z).composableMap

/-- The forward cartesian roundtrip comparison preserves composition. -/
theorem cartesianRoundtripHom_map_c {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Z.obj.left.c ≫ (arrowToTarget Z).hom.left =
      cartesianRoundtripHomComposableMap Z ≫ actionComposition (toActionObj Z) :=
  (cartesianRoundtripHom Z).map_c

/-- The inverse comparison with the action-groupoid reconstruction preserves source. -/
theorem cartesianRoundtripInv_map_s {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    actionSource (toActionObj Z) ≫ 𝟙 Z.obj.left.U =
      (arrowToTarget Z).inv.left ≫ Z.obj.left.s := sorry

/-- The inverse comparison with the action-groupoid reconstruction preserves target. -/
theorem cartesianRoundtripInv_map_t {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    actionTarget (toActionObj Z) ≫ 𝟙 Z.obj.left.U =
      (arrowToTarget Z).inv.left ≫ Z.obj.left.t := sorry

/-- The inverse comparison with the action-groupoid reconstruction. -/
noncomputable def cartesianRoundtripInv {S : Scheme.{u}}
    {G : GroupoidScheme S} (Z : GroupoidScheme.CartesianOver G) :
    GroupoidScheme.Hom (actionGroupoid (toActionObj Z)) Z.obj.left where
  obj := 𝟙 Z.obj.left.U
  arrow := (arrowToTarget Z).inv.left
  map_s := cartesianRoundtripInv_map_s Z
  map_t := cartesianRoundtripInv_map_t Z
  map_c := by sorry

/-- The map on composable arrows induced by the inverse cartesian roundtrip comparison. -/
noncomputable def cartesianRoundtripInvComposableMap {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    Limits.pullback (actionSource (toActionObj Z)) (actionTarget (toActionObj Z)) ⟶
      Limits.pullback Z.obj.left.s Z.obj.left.t :=
  (cartesianRoundtripInv Z).composableMap

/-- The inverse cartesian roundtrip comparison preserves composition. -/
theorem cartesianRoundtripInv_map_c {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    actionComposition (toActionObj Z) ≫ (arrowToTarget Z).inv.left =
      cartesianRoundtripInvComposableMap Z ≫ Z.obj.left.c :=
  (cartesianRoundtripInv Z).map_c

/-- The two cartesian roundtrip comparisons compose to the identity on the original object. -/
theorem cartesianRoundtrip_hom_inv_id {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    GroupoidScheme.Hom.comp (cartesianRoundtripHom Z) (cartesianRoundtripInv Z) =
      GroupoidScheme.Hom.id Z.obj.left := sorry

/-- The two cartesian roundtrip comparisons compose to the identity on the reconstructed object. -/
theorem cartesianRoundtrip_inv_hom_id {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    GroupoidScheme.Hom.comp (cartesianRoundtripInv Z) (cartesianRoundtripHom Z) =
      GroupoidScheme.Hom.id (actionGroupoid (toActionObj Z)) := sorry

/-- The groupoid-scheme isomorphism underlying the cartesian roundtrip comparison. -/
noncomputable def cartesianRoundtripGroupoidIso {S : Scheme.{u}}
    {G : GroupoidScheme S} (Z : GroupoidScheme.CartesianOver G) :
    (Z.obj.left : GroupoidScheme.category S) ≅
      (actionGroupoid (toActionObj Z) : GroupoidScheme.category S) where
  hom := cartesianRoundtripHom Z
  inv := cartesianRoundtripInv Z
  hom_inv_id := cartesianRoundtrip_hom_inv_id Z
  inv_hom_id := cartesianRoundtrip_inv_hom_id Z

/-- The cartesian roundtrip comparison commutes with the structure morphisms to `G`. -/
theorem cartesianRoundtripGroupoidIso_w {S : Scheme.{u}} {G : GroupoidScheme S}
    (Z : GroupoidScheme.CartesianOver G) :
    GroupoidScheme.Hom.comp (cartesianRoundtripGroupoidIso Z).hom
      (actionGroupoidHom (toActionObj Z)) = Z.obj.hom := sorry

/-- The component of the cartesian-to-action-to-cartesian unit isomorphism. -/
noncomputable def cartesianRoundtripIso {S : Scheme.{u}}
    {G : GroupoidScheme S} (Z : GroupoidScheme.CartesianOver G) :
    Z ≅ fromActionObj (toActionObj Z) :=
  ObjectProperty.isoMk
    (fun X : GroupoidScheme.overCategory G ↦ X.hom.IsCartesian)
    (Over.isoMk (cartesianRoundtripGroupoidIso Z) (cartesianRoundtripGroupoidIso_w Z))

/-- The cartesian roundtrip components are natural. -/
theorem cartesianRoundtripIso_naturality {S : Scheme.{u}} {G : GroupoidScheme S}
    {Z W : GroupoidScheme.CartesianOver G} (a : Z ⟶ W) :
    a ≫ (cartesianRoundtripIso W).hom =
      (cartesianRoundtripIso Z).hom ≫ fromActionMap (toActionMap a) := sorry

/-- The unit isomorphism of the cartesian/action equivalence. -/
noncomputable def cartesianActionUnitIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    𝟭 (GroupoidScheme.CartesianOver G) ≅ toAction G ⋙ fromAction G :=
  NatIso.ofComponents cartesianRoundtripIso cartesianRoundtripIso_naturality

/-- The underlying object comparison for the action roundtrip. -/
noncomputable def actionRoundtripUnderlyingIso {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    GroupoidScheme.Action.obj (toActionObj (fromActionObj A)) ≅
      GroupoidScheme.Action.obj A :=
  Over.isoMk (Iso.refl _) (by sorry)

/-- The forward action-roundtrip comparison forms the canonical commutative square with the
action isomorphisms. -/
theorem actionRoundtripHom_compatibility {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    CommSq (GroupoidScheme.Action.iso (toActionObj (fromActionObj A))).hom
      ((Over.pullback G.t).map (actionRoundtripUnderlyingIso A).hom)
      ((Over.pullback G.s).map (actionRoundtripUnderlyingIso A).hom)
      (GroupoidScheme.Action.iso A).hom := sorry

/-- The inverse action-roundtrip comparison forms the canonical commutative square with the
action isomorphisms. -/
theorem actionRoundtripInv_compatibility {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    CommSq (GroupoidScheme.Action.iso A).hom
      ((Over.pullback G.t).map (actionRoundtripUnderlyingIso A).inv)
      ((Over.pullback G.s).map (actionRoundtripUnderlyingIso A).inv)
      (GroupoidScheme.Action.iso (toActionObj (fromActionObj A))).hom := sorry

/-- The two action-roundtrip maps compose to the identity on the reconstructed action. -/
theorem actionRoundtrip_hom_inv_id {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    GroupoidScheme.Action.System.Hom.ofMap (actionRoundtripUnderlyingIso A).hom
          (actionRoundtripHom_compatibility A) ≫
        GroupoidScheme.Action.System.Hom.ofMap (actionRoundtripUnderlyingIso A).inv
          (actionRoundtripInv_compatibility A) =
      𝟙 (toActionObj (fromActionObj A)) := sorry

/-- The two action-roundtrip maps compose to the identity on the original action. -/
theorem actionRoundtrip_inv_hom_id {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    GroupoidScheme.Action.System.Hom.ofMap (actionRoundtripUnderlyingIso A).inv
          (actionRoundtripInv_compatibility A) ≫
        GroupoidScheme.Action.System.Hom.ofMap (actionRoundtripUnderlyingIso A).hom
          (actionRoundtripHom_compatibility A) =
      𝟙 A := sorry

/-- The component of the action-to-cartesian-to-action counit isomorphism. -/
noncomputable def actionRoundtripIso {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) : toActionObj (fromActionObj A) ≅ A where
  hom := GroupoidScheme.Action.System.Hom.ofMap (actionRoundtripUnderlyingIso A).hom
    (actionRoundtripHom_compatibility A)
  inv := GroupoidScheme.Action.System.Hom.ofMap (actionRoundtripUnderlyingIso A).inv
    (actionRoundtripInv_compatibility A)
  hom_inv_id := actionRoundtrip_hom_inv_id A
  inv_hom_id := actionRoundtrip_inv_hom_id A

/-- The action roundtrip components are natural. -/
theorem actionRoundtripIso_naturality {S : Scheme.{u}} {G : GroupoidScheme S}
    {A B : GroupoidScheme.Action G} (a : A ⟶ B) :
    toActionMap (fromActionMap a) ≫ (actionRoundtripIso B).hom =
      (actionRoundtripIso A).hom ≫ a := sorry

/-- The counit isomorphism of the cartesian/action equivalence. -/
noncomputable def cartesianActionCounitIso {S : Scheme.{u}}
    (G : GroupoidScheme S) : fromAction G ⋙ toAction G ≅ 𝟭 (GroupoidScheme.Action G) :=
  NatIso.ofComponents actionRoundtripIso actionRoundtripIso_naturality

/-- The explicit cartesian/action unit and counit satisfy the triangle law. -/
theorem cartesianAction_triangle {S : Scheme.{u}} (G : GroupoidScheme S) :
    ∀ Z,
      (toAction G).map ((cartesianActionUnitIso G).hom.app Z) ≫
          (cartesianActionCounitIso G).hom.app ((toAction G).obj Z) =
        𝟙 ((toAction G).obj Z) := sorry

/-- The concrete equivalence between cartesian groupoid schemes and groupoid actions. -/
noncomputable def cartesianActionEquivalence {S : Scheme.{u}}
    (G : GroupoidScheme S) : GroupoidScheme.CartesianOver G ≌ GroupoidScheme.Action G where
  functor := toAction G
  inverse := fromAction G
  unitIso := cartesianActionUnitIso G
  counitIso := cartesianActionCounitIso G
  functor_unitIso_comp := cartesianAction_triangle G

end AlgebraicGeometry.GroupoidScheme.CartesianOver
