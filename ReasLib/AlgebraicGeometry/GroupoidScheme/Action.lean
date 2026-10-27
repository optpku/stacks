/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.BaseChange
public import ReasLib.AlgebraicGeometry.GroupScheme.Action

/-!
# Action groupoids of schemes

This module constructs the internal groupoid scheme associated to an action of a group scheme.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ModObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The source map `(g, x) ↦ x` of an action groupoid. -/
def actionSource {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    G.X ⊗ X.X ⟶ X.X :=
  snd G.X X.X

/-- The target map `(g, x) ↦ g • x` of an action groupoid. -/
def actionTarget {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    G.X ⊗ X.X ⟶ X.X :=
  γ[G.X, X.X]

/-- The composition map `((g, x), (g', x')) ↦ (g * g', x')` of an action groupoid. -/
def actionComposition {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    pullback (actionSource G X) (actionTarget G X) ⟶ G.X ⊗ X.X :=
  lift
    (lift
        (pullback.fst (actionSource G X) (actionTarget G X) ≫ fst G.X X.X)
        (pullback.snd (actionSource G X) (actionTarget G X) ≫ fst G.X X.X) ≫
      μ[G.X])
    (pullback.snd (actionSource G X) (actionTarget G X) ≫ snd G.X X.X)

/-- The identity map `x ↦ (1, x)` of an action groupoid. -/
def actionIdentity {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    X.X ⟶ G.X ⊗ X.X :=
  lift (toUnit X.X ≫ η[G.X]) (𝟙 X.X)

/-- The inverse map `(g, x) ↦ (g⁻¹, g • x)` of an action groupoid. -/
def actionInverse {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    G.X ⊗ X.X ⟶ G.X ⊗ X.X :=
  lift (fst G.X X.X ≫ ι[G.X]) (γ[G.X, X.X])

/-- Composition in an action groupoid has the source of its second arrow. -/
theorem ofActionCompSource {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    actionComposition G X ≫ actionSource G X =
      pullback.snd (actionSource G X) (actionTarget G X) ≫ actionSource G X := by
  simp [actionComposition, actionSource]

/-- Composition in an action groupoid has the target of its first arrow. -/
theorem ofActionCompTarget {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    actionComposition G X ≫ actionTarget G X =
      pullback.fst (actionSource G X) (actionTarget G X) ≫ actionTarget G X := by
  let a := pullback.fst (actionSource G X) (actionTarget G X)
  let b := pullback.snd (actionSource G X) (actionTarget G X)
  have h : a ≫ snd G.X X.X = (b ≫ fst G.X X.X) • (b ≫ snd G.X X.X) := by
    change a ≫ snd G.X X.X = lift (b ≫ fst G.X X.X) (b ≫ snd G.X X.X) ≫ γ[G.X, X.X]
    rw [lift_comp_fst_snd]
    exact pullback.condition
  change ((a ≫ fst G.X X.X) * (b ≫ fst G.X X.X)) • (b ≫ snd G.X X.X) =
    a ≫ γ[G.X, X.X]
  rw [← smul_smul, ← h]
  change lift (a ≫ fst G.X X.X) (a ≫ snd G.X X.X) ≫ γ[G.X, X.X] = a ≫ γ[G.X, X.X]
  rw [lift_comp_fst_snd]

/-- The identity arrow of an action groupoid has the prescribed source. -/
theorem ofActionUnitSource {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    actionIdentity G X ≫ actionSource G X = 𝟙 X.X := by
  simp [actionIdentity, actionSource]

/-- The identity arrow of an action groupoid has the prescribed target. -/
theorem ofActionUnitTarget {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    actionIdentity G X ≫ actionTarget G X = 𝟙 X.X := by
  change (1 : X.X ⟶ G.X) • (𝟙 X.X) = 𝟙 X.X
  exact _root_.one_smul _ _

/-- Inversion in an action groupoid exchanges source and target. -/
theorem ofActionInvSource {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    actionInverse G X ≫ actionSource G X = actionTarget G X := by
  simp [actionInverse, actionSource, actionTarget]

/-- Inversion in an action groupoid exchanges target and source. -/
theorem ofActionInvTarget {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    actionInverse G X ≫ actionTarget G X = actionSource G X := by
  have h : actionTarget G X = (fst G.X X.X) • (snd G.X X.X) := by
    simp [actionTarget, Hom.smul_def]
  change (fst G.X X.X)⁻¹ • actionTarget G X = snd G.X X.X
  rw [h]
  exact inv_smul_smul _ _

/-- Composition in an action groupoid is associative on every scheme of points. -/
theorem ofActionAssociativity {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    ∀ {T : Over B} (a b d : T ⟶ G.X ⊗ X.X)
      (h_ab : a ≫ actionSource G X = b ≫ actionTarget G X)
      (h_bd : b ≫ actionSource G X = d ≫ actionTarget G X)
      (h_ab_d : (pullback.lift a b h_ab ≫ actionComposition G X) ≫ actionSource G X =
        d ≫ actionTarget G X)
      (h_a_bd : a ≫ actionSource G X =
        (pullback.lift b d h_bd ≫ actionComposition G X) ≫ actionTarget G X),
      pullback.lift (pullback.lift a b h_ab ≫ actionComposition G X) d h_ab_d ≫
          actionComposition G X =
        pullback.lift a (pullback.lift b d h_bd ≫ actionComposition G X) h_a_bd ≫
          actionComposition G X := by
  intro T a b d h_ab h_bd h_ab_d h_a_bd
  apply CartesianMonoidalCategory.hom_ext
  · simp [actionComposition, comp_lift_assoc, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, MonObj.lift_lift_assoc]
  · simp [actionComposition, pullback.lift_snd_assoc]

/-- Composition in an action groupoid has the right identity law. -/
theorem ofActionRightIdentity {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : a ≫ actionSource G X =
        ((a ≫ actionSource G X) ≫ actionIdentity G X) ≫ actionTarget G X),
      pullback.lift a ((a ≫ actionSource G X) ≫ actionIdentity G X) h ≫
        actionComposition G X = a := by
  intro T a h
  apply CartesianMonoidalCategory.hom_ext
  · simp [actionComposition, actionIdentity, comp_lift_assoc, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]
  · simp [actionComposition, actionIdentity, actionSource, pullback.lift_snd_assoc]

/-- Composition in an action groupoid has the left identity law. -/
theorem ofActionLeftIdentity {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : ((a ≫ actionTarget G X) ≫ actionIdentity G X) ≫ actionSource G X =
        a ≫ actionTarget G X),
      pullback.lift ((a ≫ actionTarget G X) ≫ actionIdentity G X) a h ≫
        actionComposition G X = a := by
  intro T a h
  apply CartesianMonoidalCategory.hom_ext
  · simp [actionComposition, actionIdentity, comp_lift_assoc, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]
  · simp [actionComposition, pullback.lift_snd_assoc]

/-- An arrow followed by its inverse in an action groupoid is the identity at its target. -/
theorem ofActionInverseComp {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : a ≫ actionSource G X = (a ≫ actionInverse G X) ≫ actionTarget G X),
      pullback.lift a (a ≫ actionInverse G X) h ≫ actionComposition G X =
        (a ≫ actionTarget G X) ≫ actionIdentity G X := by
  intro T a h
  apply CartesianMonoidalCategory.hom_ext
  · simp only [actionComposition, actionInverse, actionIdentity, Category.assoc, lift_fst,
      comp_lift_assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      comp_toUnit_assoc]
    change (a ≫ fst G.X X.X) * (a ≫ fst G.X X.X)⁻¹ = 1
    exact mul_inv_cancel _
  · simp [actionComposition, actionInverse, actionIdentity, actionTarget,
      pullback.lift_snd_assoc]

/-- An inverse followed by its arrow in an action groupoid is the identity at its source. -/
theorem ofActionCompInverse {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : (a ≫ actionInverse G X) ≫ actionSource G X = a ≫ actionTarget G X),
      pullback.lift (a ≫ actionInverse G X) a h ≫ actionComposition G X =
        (a ≫ actionSource G X) ≫ actionIdentity G X := by
  intro T a h
  apply CartesianMonoidalCategory.hom_ext
  · simp only [actionComposition, actionInverse, actionIdentity, Category.assoc, lift_fst,
      comp_lift_assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      comp_toUnit_assoc]
    change (a ≫ fst G.X X.X)⁻¹ * (a ≫ fst G.X X.X) = 1
    exact inv_mul_cancel _
  · simp [actionComposition, actionIdentity, actionSource, pullback.lift_snd_assoc]

/-- The groupoid scheme associated to an action of a group scheme. -/
def ofAction {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) : GroupoidScheme B where
  U := X.X
  R := G.X ⊗ X.X
  s := actionSource G X
  t := actionTarget G X
  e := actionIdentity G X
  i := actionInverse G X
  c := actionComposition G X
  comp_source := ofActionCompSource G X
  comp_target := ofActionCompTarget G X
  identity_source := ofActionUnitSource G X
  identity_target := ofActionUnitTarget G X
  inverse_source := ofActionInvSource G X
  inverse_target := ofActionInvTarget G X
  associativity := ofActionAssociativity G X
  right_identity := ofActionRightIdentity G X
  left_identity := ofActionLeftIdentity G X
  inverse_comp := ofActionInverseComp G X
  comp_inverse := ofActionCompInverse G X

/-- The object scheme of the action groupoid is the acted-on object. -/
theorem ofAction_U {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    (ofAction G X).U = X.X := rfl

/-- The arrow scheme of the action groupoid is `G.X ⊗ X.X`. -/
theorem ofAction_R {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    (ofAction G X).R = G.X ⊗ X.X := rfl

/-- The source map of the action groupoid is `(g, x) ↦ x`. -/
theorem ofAction_s {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    (ofAction G X).s = actionSource G X := rfl

/-- The target map of the action groupoid is the action map. -/
theorem ofAction_t {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    (ofAction G X).t = actionTarget G X := rfl

/-- The composition map of the action groupoid multiplies the group components. -/
theorem ofAction_c {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    (ofAction G X).c = actionComposition G X := rfl

/-- The identity map of the action groupoid inserts the group identity. -/
theorem ofAction_e {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    (ofAction G X).e = actionIdentity G X := rfl

/-- The inverse map of the action groupoid inverts the group component and acts on the object. -/
theorem ofAction_i {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :
    (ofAction G X).i = actionInverse G X := rfl

/-- The action groupoid over `Y`, regarded over `S` through the structure map `Y ⟶ S`. -/
def action {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) : GroupoidScheme S :=
  changeBase Y.hom (ofAction G X)

/-- The object scheme of an action groupoid over `S` is `X` regarded over `S`. -/
theorem action_U {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    (action Y G X).U = (Over.map Y.hom).obj X.X := rfl

/-- The arrow scheme is `G.X ⊗ X.X` over `Y`, regarded over `S`. -/
theorem action_R {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    (action Y G X).R = (Over.map Y.hom).obj (G.X ⊗ X.X) := rfl

/-- The source map of an action groupoid is the mapped projection `(g, x) ↦ x`. -/
theorem action_s {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    (action Y G X).s = (Over.map Y.hom).map (actionSource G X) := rfl

/-- The target map of an action groupoid is the mapped action `(g, x) ↦ g • x`. -/
theorem action_t {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    (action Y G X).t = (Over.map Y.hom).map (actionTarget G X) := rfl

/-- Composition in an action groupoid is the mapped group multiplication formula. -/
theorem action_c {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    (action Y G X).c =
      changeBaseComposable Y.hom (ofAction G X) ≫
        (Over.map Y.hom).map (actionComposition G X) := rfl

/-- The identity map of an action groupoid is the mapped formula `x ↦ (1, x)`. -/
theorem action_e {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    (action Y G X).e = (Over.map Y.hom).map (actionIdentity G X) := rfl

/-- The inverse map of an action groupoid is the mapped formula `(g, x) ↦ (g⁻¹, g • x)`. -/
theorem action_i {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    (action Y G X).i = (Over.map Y.hom).map (actionInverse G X) := rfl

end AlgebraicGeometry.GroupoidScheme
