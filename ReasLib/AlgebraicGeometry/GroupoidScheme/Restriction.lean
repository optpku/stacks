/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback

/-!
# Restriction of a groupoid scheme

This module constructs the restriction of a groupoid scheme along a morphism to its object
scheme, together with its canonical morphism to the original groupoid scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The canonical map from the arrows of a restricted groupoid to the original arrows. -/
def pullbackArrow {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : (G.toPreRelation.pullback g).left ⟶ G.R :=
  Limits.pullback.fst G.toPreRelation.hom (prod.map g g)

/-- The arrow projection from a restriction commutes with source maps. -/
theorem pullbackArrow_s {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    pullbackArrow G g ≫ G.s = (G.toPreRelation.pullback g).s ≫ g := sorry

/-- The arrow projection from a restriction commutes with target maps. -/
theorem pullbackArrow_t {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    pullbackArrow G g ≫ G.t = (G.toPreRelation.pullback g).t ≫ g := sorry

/-- The original identity arrow and the diagonal of `U'` define a point of the restricted
arrow pullback. -/
theorem pullbackIdentity_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (g ≫ G.e) ≫ G.toPreRelation.hom = diag U' ≫ prod.map g g := sorry

/-- The identity-arrow map of the restricted groupoid. -/
def pullbackIdentity {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : U' ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift (g ≫ G.e) (diag U') (pullbackIdentity_condition G g)

/-- The restricted identity arrow has each endpoint equal to its object. -/
theorem pullbackIdentity_spec {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    pullbackIdentity G g ≫ (G.toPreRelation.pullback g).s = 𝟙 U' ∧
      pullbackIdentity G g ≫ (G.toPreRelation.pullback g).t = 𝟙 U' := sorry

/-- Applying the original inverse and exchanging the two endpoints defines an arrow of the
restricted groupoid. -/
theorem pullbackInverse_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrow G g ≫ G.i) ≫ G.toPreRelation.hom =
      prod.lift (G.toPreRelation.pullback g).s (G.toPreRelation.pullback g).t ≫
        prod.map g g := sorry

/-- The inverse-arrow map of the restricted groupoid. -/
def pullbackInverse {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift (pullbackArrow G g ≫ G.i)
    (prod.lift (G.toPreRelation.pullback g).s (G.toPreRelation.pullback g).t)
    (pullbackInverse_condition G g)

/-- Restricted inversion exchanges source and target. -/
theorem pullbackInverse_spec {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    pullbackInverse G g ≫ (G.toPreRelation.pullback g).s =
        (G.toPreRelation.pullback g).t ∧
      pullbackInverse G g ≫ (G.toPreRelation.pullback g).t =
        (G.toPreRelation.pullback g).s := sorry

/-- The images in `G` of two composable restricted arrows remain composable. -/
theorem pullbackCompositionToArrows_condition {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U) :
    (Limits.pullback.fst (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.s =
      (Limits.pullback.snd (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.t := sorry

/-- Compose a pair of restricted arrows in the original groupoid. -/
def pullbackCompositionToArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
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
theorem pullbackComposition_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    pullbackCompositionToArrows G g ≫ G.toPreRelation.hom =
      prod.lift
          (Limits.pullback.fst (G.toPreRelation.pullback g).s
            (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).t)
          (Limits.pullback.snd (G.toPreRelation.pullback g).s
            (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).s) ≫
        prod.map g g := sorry

/-- The canonical composition law on the restricted arrow scheme. -/
def pullbackComposition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
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
theorem pullbackComposition_spec {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    pullbackComposition G g ≫ (G.toPreRelation.pullback g).s =
        Limits.pullback.snd (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).s ∧
      pullbackComposition G g ≫ (G.toPreRelation.pullback g).t =
        Limits.pullback.fst (G.toPreRelation.pullback g).s
          (G.toPreRelation.pullback g).t ≫ (G.toPreRelation.pullback g).t := sorry

/-- Restriction of a groupoid scheme along a morphism to its object scheme. -/
def pullback {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : GroupoidScheme S where
  U := U'
  R := (G.toPreRelation.pullback g).left
  s := (G.toPreRelation.pullback g).s
  t := (G.toPreRelation.pullback g).t
  c := pullbackComposition G g
  e := pullbackIdentity G g
  i := pullbackInverse G g
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object scheme of the restriction is `U'`. -/
theorem pullback_U {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : (pullback G g).U = U' := sorry

/-- The arrow scheme of the restriction is the pullback of the underlying pre-relation. -/
theorem pullback_R {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    (pullback G g).R = (G.toPreRelation.pullback g).left := sorry

/-- Forgetting a restricted groupoid scheme to its underlying pre-relation agrees with
pulling back the underlying pre-relation. -/
theorem pullback_toPreRelation {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.pullback g).toPreRelation = G.toPreRelation.pullback g := by
  change Scheme.PreRelation.ofHom
      (Limits.prod.lift (G.toPreRelation.pullback g).t (G.toPreRelation.pullback g).s) =
    Scheme.PreRelation.ofHom (G.toPreRelation.pullback g).hom
  rw [Scheme.PreRelation.hom_eq_prod_lift]

/-- The composition of the restriction is the canonical pullback composition. -/
theorem pullback_c {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : (pullback G g).c = pullbackComposition G g := sorry

/-- The canonical morphism from the restricted groupoid scheme to the original groupoid. -/
def pullbackHom {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : Hom (pullback G g) G where
  obj := g
  arrow := pullbackArrow G g
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The canonical restriction morphism uses `g` on objects and the pullback projection on
arrows. -/
theorem pullbackHom_spec {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    (pullbackHom G g).obj = g ∧ (pullbackHom G g).arrow = pullbackArrow G g := sorry

end AlgebraicGeometry.GroupoidScheme
