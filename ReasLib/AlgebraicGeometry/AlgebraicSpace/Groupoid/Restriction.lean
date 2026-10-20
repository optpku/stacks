/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Restriction of groupoids in algebraic spaces

The arrow pullback and its induced groupoid structure over the base algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The canonical map from the arrows of a restricted groupoid to the original arrows. -/
def pullbackArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ G.R :=
  Limits.pullback.fst G.toPreRelation.hom (prod.map g g)

/-- The arrow projection from a restriction commutes with source maps. -/
theorem pullbackArrow_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackArrow G g ≫ G.s = (G.toPreRelation.pullback g).s ≫ g := sorry

/-- The arrow projection from a restriction commutes with target maps. -/
theorem pullbackArrow_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackArrow G g ≫ G.t = (G.toPreRelation.pullback g).t ≫ g := sorry

/-- The original identity arrow and the diagonal of `U'` define a point of the restricted
arrow pullback. -/
theorem pullbackIdentity_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (g ≫ G.e) ≫ G.toPreRelation.hom = diag U' ≫ prod.map g g := sorry

/-- The identity-arrow map of the restricted groupoid. -/
def pullbackIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    U' ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift (g ≫ G.e) (diag U') (pullbackIdentity_condition G g)

/-- The restricted identity arrow has each endpoint equal to its object. -/
theorem pullbackIdentity_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackIdentity G g ≫ (G.toPreRelation.pullback g).s = 𝟙 U' ∧
      pullbackIdentity G g ≫ (G.toPreRelation.pullback g).t = 𝟙 U' := sorry

/-- Applying the original inverse and exchanging the two endpoints defines an arrow of the
restricted groupoid. -/
theorem pullbackInverse_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullbackArrow G g ≫ G.i) ≫ G.toPreRelation.hom =
      prod.lift (G.toPreRelation.pullback g).s (G.toPreRelation.pullback g).t ≫
        prod.map g g := sorry

/-- The inverse-arrow map of the restricted groupoid. -/
def pullbackInverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift (pullbackArrow G g ≫ G.i)
    (prod.lift (G.toPreRelation.pullback g).s (G.toPreRelation.pullback g).t)
    (pullbackInverse_condition G g)

/-- Restricted inversion exchanges source and target. -/
theorem pullbackInverse_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackInverse G g ≫ (G.toPreRelation.pullback g).s =
        (G.toPreRelation.pullback g).t ∧
      pullbackInverse G g ≫ (G.toPreRelation.pullback g).t =
        (G.toPreRelation.pullback g).s := sorry

/-- The images in `G` of two composable restricted arrows remain composable. -/
theorem pullbackCompositionToArrows_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (Limits.pullback.fst (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.s =
      (Limits.pullback.snd (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.t := sorry

/-- Compose a pair of restricted arrows in the original groupoid. -/
def pullbackCompositionToArrows {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    Limits.pullback (G.toPreRelation.pullback g).s
        (G.toPreRelation.pullback g).t ⟶ G.R :=
  Limits.pullback.lift
      (Limits.pullback.fst (G.toPreRelation.pullback g).s
        (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
      (Limits.pullback.snd (G.toPreRelation.pullback g).s
        (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
      (pullbackCompositionToArrows_condition G g) ≫ G.c

/-- The original composite and its two endpoints define a point of the restricted arrow
pullback. -/
theorem pullbackComposition_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackCompositionToArrows G g ≫ G.toPreRelation.hom =
      prod.lift
          (Limits.pullback.fst (G.toPreRelation.pullback g).s
            (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).t)
          (Limits.pullback.snd (G.toPreRelation.pullback g).s
            (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).s) ≫
        prod.map g g := sorry

/-- The canonical composition law on the restricted arrow space. -/
def pullbackComposition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    Limits.pullback (G.toPreRelation.pullback g).s
        (G.toPreRelation.pullback g).t ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift (pullbackCompositionToArrows G g)
    (prod.lift
      (Limits.pullback.fst (G.toPreRelation.pullback g).s
        (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).t)
      (Limits.pullback.snd (G.toPreRelation.pullback g).s
        (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).s))
    (pullbackComposition_condition G g)

/-- Restricted composition has the source of its second arrow and target of its first arrow. -/
theorem pullbackComposition_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackComposition G g ≫ (G.toPreRelation.pullback g).s =
        Limits.pullback.snd (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).s ∧
      pullbackComposition G g ≫ (G.toPreRelation.pullback g).t =
        Limits.pullback.fst (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).t := sorry

/-- Composition of restricted arrows is associative. -/
theorem pullback_associativity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    ∀ {T : Over B} (a b d : T ⟶ (G.toPreRelation.pullback g).left)
      (h_ab : a ≫ (G.toPreRelation.pullback g).s = b ≫ (G.toPreRelation.pullback g).t)
      (h_bd : b ≫ (G.toPreRelation.pullback g).s = d ≫ (G.toPreRelation.pullback g).t)
      (h_ab_d : (Limits.pullback.lift a b h_ab ≫ pullbackComposition G g) ≫
        (G.toPreRelation.pullback g).s = d ≫ (G.toPreRelation.pullback g).t)
      (h_a_bd : a ≫ (G.toPreRelation.pullback g).s =
        (Limits.pullback.lift b d h_bd ≫ pullbackComposition G g) ≫
          (G.toPreRelation.pullback g).t),
      Limits.pullback.lift (Limits.pullback.lift a b h_ab ≫ pullbackComposition G g)
          d h_ab_d ≫ pullbackComposition G g =
        Limits.pullback.lift a (Limits.pullback.lift b d h_bd ≫
          pullbackComposition G g) h_a_bd ≫ pullbackComposition G g := sorry

/-- The restricted identity is a right unit for composition. -/
theorem pullback_right_identity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    ∀ {T : Over B} (a : T ⟶ (G.toPreRelation.pullback g).left)
      (h : a ≫ (G.toPreRelation.pullback g).s =
        ((a ≫ (G.toPreRelation.pullback g).s) ≫ pullbackIdentity G g) ≫
          (G.toPreRelation.pullback g).t),
      Limits.pullback.lift a ((a ≫ (G.toPreRelation.pullback g).s) ≫
        pullbackIdentity G g) h ≫ pullbackComposition G g = a := sorry

/-- The restricted identity is a left unit for composition. -/
theorem pullback_left_identity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    ∀ {T : Over B} (a : T ⟶ (G.toPreRelation.pullback g).left)
      (h : ((a ≫ (G.toPreRelation.pullback g).t) ≫ pullbackIdentity G g) ≫
        (G.toPreRelation.pullback g).s = a ≫ (G.toPreRelation.pullback g).t),
      Limits.pullback.lift ((a ≫ (G.toPreRelation.pullback g).t) ≫
        pullbackIdentity G g) a h ≫ pullbackComposition G g = a := sorry

/-- Composing a restricted arrow with its inverse gives its target identity. -/
theorem pullback_inverse_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    ∀ {T : Over B} (a : T ⟶ (G.toPreRelation.pullback g).left)
      (h : a ≫ (G.toPreRelation.pullback g).s =
        (a ≫ pullbackInverse G g) ≫ (G.toPreRelation.pullback g).t),
      Limits.pullback.lift a (a ≫ pullbackInverse G g) h ≫
        pullbackComposition G g =
          (a ≫ (G.toPreRelation.pullback g).t) ≫ pullbackIdentity G g := sorry

/-- Composing an inverse restricted arrow with its original gives its source identity. -/
theorem pullback_comp_inverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    ∀ {T : Over B} (a : T ⟶ (G.toPreRelation.pullback g).left)
      (h : (a ≫ pullbackInverse G g) ≫ (G.toPreRelation.pullback g).s =
        a ≫ (G.toPreRelation.pullback g).t),
      Limits.pullback.lift (a ≫ pullbackInverse G g) a h ≫
        pullbackComposition G g =
          (a ≫ (G.toPreRelation.pullback g).s) ≫ pullbackIdentity G g := sorry

/-- Restriction of a groupoid in algebraic spaces along a morphism to its object space. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    GroupoidAlgebraicSpace B where
  U := U'
  R := (G.toPreRelation.pullback g).left
  s := (G.toPreRelation.pullback g).s
  t := (G.toPreRelation.pullback g).t
  c := pullbackComposition G g
  e := pullbackIdentity G g
  i := pullbackInverse G g
  comp_source := (pullbackComposition_spec G g).1
  comp_target := (pullbackComposition_spec G g).2
  identity_source := (pullbackIdentity_spec G g).1
  identity_target := (pullbackIdentity_spec G g).2
  inverse_source := (pullbackInverse_spec G g).1
  inverse_target := (pullbackInverse_spec G g).2
  associativity := pullback_associativity G g
  right_identity := pullback_right_identity G g
  left_identity := pullback_left_identity G g
  inverse_comp := pullback_inverse_comp G g
  comp_inverse := pullback_comp_inverse G g

/-- The object space of the restriction is `U'`. -/
theorem pullback_U {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullback G g).U = U' := sorry

/-- The arrow space of the restriction is the pullback of the underlying pre-relation. -/
theorem pullback_R {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullback G g).R = (G.toPreRelation.pullback g).left := sorry

/-- Forgetting a restricted groupoid in algebraic spaces to its underlying pre-relation
agrees with pulling back the underlying pre-relation. -/
theorem pullback_toPreRelation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.pullback g).toPreRelation = G.toPreRelation.pullback g := sorry

/-- The composition of the restriction is the canonical pullback composition. -/
theorem pullback_c {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullback G g).c = pullbackComposition G g := sorry

/-- The arrow projection preserves the composition of restricted arrows. -/
theorem pullbackHom_map_c {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullback G g).c ≫ pullbackArrow G g =
      composableMap g (pullbackArrow G g)
        (Eq.symm (pullbackArrow_s G g)) (Eq.symm (pullbackArrow_t G g)) ≫ G.c := sorry

/-- The canonical morphism from the restricted groupoid to the original groupoid. -/
def pullbackHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    Hom (pullback G g) G where
  obj := g
  arrow := pullbackArrow G g
  map_s := (pullbackArrow_s G g).symm
  map_t := (pullbackArrow_t G g).symm
  map_c := pullbackHom_map_c G g

/-- The canonical restriction morphism uses `g` on objects and the pullback projection on
arrows. -/
theorem pullbackHom_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullbackHom G g).obj = g ∧ (pullbackHom G g).arrow = pullbackArrow G g := sorry

/-- Restrict along a map of algebraic spaces to the object space. -/
def pullbackAlong {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : AlgebraicSpace S} (g : U' ⟶ G.U.left) :
    GroupoidAlgebraicSpace B :=
  pullback G (Over.homMk g rfl : Over.mk (g ≫ G.U.hom) ⟶ G.U)

/-- The restriction along a raw algebraic-space map projects to the original groupoid. -/
def pullbackAlongHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : AlgebraicSpace S} (g : U' ⟶ G.U.left) :
    Hom (pullbackAlong G g) G :=
  pullbackHom G (Over.homMk g rfl : Over.mk (g ≫ G.U.hom) ⟶ G.U)
end AlgebraicGeometry.GroupoidAlgebraicSpace
