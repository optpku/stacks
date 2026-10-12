/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid

/-!
# Action groupoids of algebraic spaces

This module constructs the internal groupoid in algebraic spaces associated to
an action of a group algebraic space.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ModObj
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The source map `(g, x) ↦ x` of an action groupoid. -/
def actionSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : G.X ⊗ X.X ⟶ X.X :=
  snd G.X X.X

/-- The target map `(g, x) ↦ a(g, x)` of an action groupoid. -/
def actionTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : G.X ⊗ X.X ⟶ X.X :=
  γ[G.X, X.X]

/-- The composition map `((g, x), (g', x')) ↦ (m(g, g'), x')` of an action groupoid. -/
def actionComposition {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) :
    pullback (actionSource G X) (actionTarget G X) ⟶ G.X ⊗ X.X :=
  lift
    (lift
        (pullback.fst (actionSource G X) (actionTarget G X) ≫ fst G.X X.X)
        (pullback.snd (actionSource G X) (actionTarget G X) ≫ fst G.X X.X) ≫
      μ[G.X])
    (pullback.snd (actionSource G X) (actionTarget G X) ≫ snd G.X X.X)

/-- The identity map `x ↦ (η[G.X](x), x)` of an action groupoid. -/
def actionIdentity {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : X.X ⟶ G.X ⊗ X.X :=
  lift (toUnit X.X ≫ η[G.X]) (𝟙 X.X)

/-- The inverse map `(g, x) ↦ (ι[G.X](g), a(g, x))` of an action groupoid. -/
def actionInverse {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : G.X ⊗ X.X ⟶ G.X ⊗ X.X :=
  lift (fst G.X X.X ≫ ι[G.X]) (γ[G.X, X.X])

/-- Composition in an action groupoid has the source of its second arrow. -/
theorem ofActionCompSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    actionComposition G X ≫ actionSource G X =
      pullback.snd (actionSource G X) (actionTarget G X) ≫ actionSource G X := sorry

/-- Composition in an action groupoid has the target of its first arrow. -/
theorem ofActionCompTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    actionComposition G X ≫ actionTarget G X =
      pullback.fst (actionSource G X) (actionTarget G X) ≫ actionTarget G X := sorry

/-- The identity arrow of an action groupoid has the prescribed source. -/
theorem ofActionUnitSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    actionIdentity G X ≫ actionSource G X = 𝟙 X.X := sorry

/-- The identity arrow of an action groupoid has the prescribed target. -/
theorem ofActionUnitTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    actionIdentity G X ≫ actionTarget G X = 𝟙 X.X := sorry

/-- Inversion in an action groupoid exchanges source and target. -/
theorem ofActionInvSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    actionInverse G X ≫ actionSource G X = actionTarget G X := sorry

/-- Inversion in an action groupoid exchanges target and source. -/
theorem ofActionInvTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    actionInverse G X ≫ actionTarget G X = actionSource G X := sorry

/-- Composition in an action groupoid is associative on every object of points. -/
theorem ofActionAssociativity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
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
          actionComposition G X := sorry

/-- Composition in an action groupoid has the right identity law. -/
theorem ofActionRightIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : a ≫ actionSource G X =
        ((a ≫ actionSource G X) ≫ actionIdentity G X) ≫ actionTarget G X),
      pullback.lift a ((a ≫ actionSource G X) ≫ actionIdentity G X) h ≫
        actionComposition G X = a := sorry

/-- Composition in an action groupoid has the left identity law. -/
theorem ofActionLeftIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : ((a ≫ actionTarget G X) ≫ actionIdentity G X) ≫ actionSource G X =
        a ≫ actionTarget G X),
      pullback.lift ((a ≫ actionTarget G X) ≫ actionIdentity G X) a h ≫
        actionComposition G X = a := sorry

/-- An arrow followed by its inverse in an action groupoid is the identity at its target. -/
theorem ofActionInverseComp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : a ≫ actionSource G X = (a ≫ actionInverse G X) ≫ actionTarget G X),
      pullback.lift a (a ≫ actionInverse G X) h ≫ actionComposition G X =
        (a ≫ actionTarget G X) ≫ actionIdentity G X := sorry

/-- An inverse followed by its arrow in an action groupoid is the identity at its source. -/
theorem ofActionCompInverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    ∀ {T : Over B} (a : T ⟶ G.X ⊗ X.X)
      (h : (a ≫ actionInverse G X) ≫ actionSource G X = a ≫ actionTarget G X),
      pullback.lift (a ≫ actionInverse G X) a h ≫ actionComposition G X =
        (a ≫ actionSource G X) ≫ actionIdentity G X := sorry

/-- The groupoid in algebraic spaces over `B` associated to an action of a group
algebraic space `G` on `X`. The object space is `X.X`, the arrow space is
`G.X ⊗ X.X`, source is `(g, x) ↦ x`, target is `(g, x) ↦ γ[G.X, X.X](g, x)`,
composition is `((g, x), (g', x')) ↦ (μ[G.X](g, g'), x')`, identity is
`x ↦ (η[G.X](x), x)`, and inverse is `(g, x) ↦ (ι[G.X](g), γ[G.X, X.X](g, x))`. -/
def ofAction {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : GroupoidAlgebraicSpace B where
  U := X.X
  R := G.X ⊗ X.X
  s := actionSource G X
  t := actionTarget G X
  c := actionComposition G X
  e := actionIdentity G X
  i := actionInverse G X
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

/-- The object space of the action groupoid is the acted-on algebraic space. -/
theorem ofAction_U {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : (ofAction G X).U = X.X := sorry

/-- The arrow space of the action groupoid is `G.X ⊗ X.X`. -/
theorem ofAction_R {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : (ofAction G X).R = G.X ⊗ X.X := sorry

/-- The source map of the action groupoid is `(g, x) ↦ x`. -/
theorem ofAction_s {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : (ofAction G X).s = actionSource G X := sorry

/-- The target map of the action groupoid is the action map. -/
theorem ofAction_t {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : (ofAction G X).t = actionTarget G X := sorry

/-- The composition map of the action groupoid multiplies the group components. -/
theorem ofAction_c {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) :
    (ofAction G X).c = actionComposition G X := sorry

/-- The identity map of the action groupoid inserts the group identity. -/
theorem ofAction_e {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : (ofAction G X).e = actionIdentity G X := sorry

/-- The inverse map of the action groupoid inverts the group component and acts on the
object. -/
theorem ofAction_i {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : (ofAction G X).i = actionInverse G X := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
