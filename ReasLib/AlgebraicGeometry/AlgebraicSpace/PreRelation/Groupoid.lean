/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Groupoid extensions of equivalence relations on algebraic spaces

An internal equivalence relation over an algebraic space determines composition, identities,
and inverses, and extends uniquely to a groupoid with the same objects and endpoint maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The canonical composition morphism on composable arrows of an internal equivalence relation
over an algebraic space. -/
def composition {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : pullback P.s P.t ⟶ P.left :=
  let hP : EquivalenceRelation P.t P.s :=
    Classical.choice
      (IsEquivalenceRelation.nonempty_equivalenceRelation :
        Nonempty (EquivalenceRelation P.t P.s))
  let T := hP.toTransitiveRelation
  PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t) (pullback.snd P.s P.t)
      pullback.condition ≫ T.t

/-- The target of `P.composition` is the target of the first composable arrow. -/
theorem composition_target {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    P.composition ≫ P.t = pullback.fst P.s P.t ≫ P.t := sorry

/-- The source of `P.composition` is the source of the second composable arrow. -/
theorem composition_source {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    P.composition ≫ P.s = pullback.snd P.s P.t ≫ P.s := sorry

/-- The composition morphism is characterized by its target and source maps. -/
theorem composition_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    P.composition ≫ P.t = pullback.fst P.s P.t ≫ P.t ∧
      P.composition ≫ P.s = pullback.snd P.s P.t ≫ P.s := sorry

/-- Any morphism with the target and source equations of `P.composition` equals it. -/
theorem eq_composition_of_target_source {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] {c : pullback P.s P.t ⟶ P.left}
    (hc_t : c ≫ P.t = pullback.fst P.s P.t ≫ P.t)
    (hc_s : c ≫ P.s = pullback.snd P.s P.t ≫ P.s) :
    c = P.composition := sorry

/-- An internal equivalence relation over an algebraic space has a unique composition on
composable arrows, characterized by its target and source. -/
theorem existsUniqueComposition {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    ∃! c : pullback P.s P.t ⟶ P.left,
      c ≫ P.t = pullback.fst P.s P.t ≫ P.t ∧
        c ≫ P.s = pullback.snd P.s P.t ≫ P.s := sorry

/-- The identity-arrow map of an internal equivalence relation is its reflexivity morphism. -/
def identity {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : U ⟶ P.left :=
  let hP : EquivalenceRelation P.t P.s :=
    Classical.choice
      (IsEquivalenceRelation.nonempty_equivalenceRelation :
        Nonempty (EquivalenceRelation P.t P.s))
  hP.toReflexiveRelation.r

/-- The inverse-arrow map of an internal equivalence relation is its symmetry morphism. -/
def inverse {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : P.left ⟶ P.left :=
  let hP : EquivalenceRelation P.t P.s :=
    Classical.choice
      (IsEquivalenceRelation.nonempty_equivalenceRelation :
        Nonempty (EquivalenceRelation P.t P.s))
  hP.toSymmetricRelation.s

/-- The source and target of an identity arrow are the original object. -/
theorem identity_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    P.identity ≫ P.s = 𝟙 U ∧ P.identity ≫ P.t = 𝟙 U := sorry

/-- Inversion exchanges the source and target of each arrow. -/
theorem inverse_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    P.inverse ≫ P.s = P.t ∧ P.inverse ≫ P.t = P.s := sorry

/-- Composition of arrows in an internal equivalence relation is associative on points. -/
theorem composition_assoc {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    ∀ {T : Over B} (later middle earlier : T ⟶ P.left)
      (h_lm : later ≫ P.s = middle ≫ P.t) (h_me : middle ≫ P.s = earlier ≫ P.t)
      (h_lm_e : (pullback.lift later middle h_lm ≫ P.composition) ≫ P.s = earlier ≫ P.t)
      (h_l_me : later ≫ P.s = (pullback.lift middle earlier h_me ≫ P.composition) ≫ P.t),
      pullback.lift (pullback.lift later middle h_lm ≫ P.composition) earlier h_lm_e ≫
          P.composition =
        pullback.lift later (pullback.lift middle earlier h_me ≫ P.composition) h_l_me ≫
          P.composition := sorry

/-- Composing an arrow after the identity at its source leaves the arrow unchanged. -/
theorem composition_identity {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    ∀ {T : Over B} (arrow : T ⟶ P.left)
      (h : arrow ≫ P.s = ((arrow ≫ P.s) ≫ P.identity) ≫ P.t),
      pullback.lift arrow ((arrow ≫ P.s) ≫ P.identity) h ≫ P.composition = arrow := sorry

/-- Composing the identity at the target of an arrow after it leaves the arrow unchanged. -/
theorem identity_composition {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    ∀ {T : Over B} (arrow : T ⟶ P.left)
      (h : ((arrow ≫ P.t) ≫ P.identity) ≫ P.s = arrow ≫ P.t),
      pullback.lift ((arrow ≫ P.t) ≫ P.identity) arrow h ≫ P.composition = arrow := sorry

/-- Composing an arrow after its inverse gives the identity at its target. -/
theorem composition_inverse {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    ∀ {T : Over B} (arrow : T ⟶ P.left)
      (h : arrow ≫ P.s = (arrow ≫ P.inverse) ≫ P.t),
      pullback.lift arrow (arrow ≫ P.inverse) h ≫ P.composition =
        (arrow ≫ P.t) ≫ P.identity := sorry

/-- Composing the inverse of an arrow after it gives the identity at its source. -/
theorem inverse_composition {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    ∀ {T : Over B} (arrow : T ⟶ P.left)
      (h : (arrow ≫ P.inverse) ≫ P.s = arrow ≫ P.t),
      pullback.lift (arrow ≫ P.inverse) arrow h ≫ P.composition =
        (arrow ≫ P.s) ≫ P.identity := sorry

/-- A groupoid extends a pre-relation when its objects, arrows, source, and target are fixed
by that pre-relation. -/
def IsGroupoidExtension {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (G : GroupoidAlgebraicSpace B) : Prop :=
  G.U = U ∧ G.R = P.left ∧ HEq G.s P.s ∧ HEq G.t P.t

/-- The groupoid on an internal equivalence relation has its canonical composition, identity,
and inverse maps. -/
def toGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] : GroupoidAlgebraicSpace B where
  U := U
  R := P.left
  s := P.s
  t := P.t
  c := P.composition
  e := P.identity
  i := P.inverse
  comp_source := P.composition_source
  comp_target := P.composition_target
  identity_source := P.identity_spec.1
  identity_target := P.identity_spec.2
  inverse_source := P.inverse_spec.1
  inverse_target := P.inverse_spec.2
  associativity := P.composition_assoc
  right_identity := P.composition_identity
  left_identity := P.identity_composition
  inverse_comp := P.composition_inverse
  comp_inverse := P.inverse_composition

/-- The canonical groupoid of an internal equivalence relation preserves its objects, arrows,
source, and target. -/
theorem toGroupoid_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    P.IsGroupoidExtension P.toGroupoid := sorry

/-- Every groupoid extending a fixed internal equivalence relation equals its canonical groupoid.
-/
theorem eq_toGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] (G : GroupoidAlgebraicSpace B)
    (hG : P.IsGroupoidExtension G) : G = P.toGroupoid := sorry

/-- An internal equivalence relation over an algebraic space extends uniquely to a groupoid with
the same objects, arrows, source, and target. -/
theorem existsUniqueGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    ∃! G : GroupoidAlgebraicSpace B, P.IsGroupoidExtension G := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
