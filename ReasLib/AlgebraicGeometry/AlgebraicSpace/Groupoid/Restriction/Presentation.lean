module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction

/-!
# Fibre-product presentation of restricted groupoid arrows

The restricted arrows identify with the iterated source and target fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The arrow space in the iterated fibre-product presentation of a restriction. -/
abbrev iteratedPullbackArrows {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) : Over B :=
  Limits.pullback (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t)

/-- The restricted arrow space maps canonically to `R ×_{s, U} U'`. -/
def pullbackToSourceSquare {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ Limits.pullback G.s g :=
  Limits.pullback.lift (pullbackArrow G g) (G.toPreRelation.pullback g).s
    (pullbackArrow_s G g)

/-- The two maps defining the canonical morphism to `U' ×_{U, t} R` commute. -/
theorem pullbackToTargetSquare_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).t ≫ g = pullbackArrow G g ≫ G.t := sorry

/-- The restricted arrow space maps canonically to `U' ×_{U, t} R`. -/
def pullbackToTargetSquare {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ Limits.pullback g G.t :=
  Limits.pullback.lift (G.toPreRelation.pullback g).t (pullbackArrow G g)
    (pullbackToTargetSquare_condition G g)

/-- The two square maps from the restricted arrow space have the same arrow projection. -/
theorem pullbackToIterated_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackToSourceSquare G g ≫ Limits.pullback.fst G.s g =
      pullbackToTargetSquare G g ≫ Limits.pullback.snd g G.t := sorry

/-- The canonical map from the single-pullback arrow space to the displayed iterated
fibre product. -/
def pullbackToIterated {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ iteratedPullbackArrows G g :=
  Limits.pullback.lift (pullbackToSourceSquare G g) (pullbackToTargetSquare G g)
    (pullbackToIterated_condition G g)

/-- The arrow and endpoint projections from the displayed iterated fibre product satisfy
the single-pullback compatibility equation. -/
theorem iteratedToPullback_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst G.s g) ≫ G.toPreRelation.hom =
      prod.lift
          (Limits.pullback.snd (Limits.pullback.fst G.s g)
              (Limits.pullback.snd g G.t) ≫ Limits.pullback.fst g G.t)
          (Limits.pullback.fst (Limits.pullback.fst G.s g)
              (Limits.pullback.snd g G.t) ≫ Limits.pullback.snd G.s g) ≫
        prod.map g g := sorry

/-- The canonical map from the displayed iterated fibre product to the single-pullback
arrow space. -/
def iteratedToPullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    iteratedPullbackArrows G g ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift
    (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst G.s g)
    (prod.lift
      (Limits.pullback.snd (Limits.pullback.fst G.s g)
          (Limits.pullback.snd g G.t) ≫ Limits.pullback.fst g G.t)
      (Limits.pullback.fst (Limits.pullback.fst G.s g)
          (Limits.pullback.snd g G.t) ≫ Limits.pullback.snd G.s g))
    (iteratedToPullback_condition G g)

/-- The two canonical comparisons compose to the identity on restricted arrows. -/
theorem pullbackArrowIso_hom_inv_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackToIterated G g ≫ iteratedToPullback G g = 𝟙 _ := sorry

/-- The two canonical comparisons compose to the identity on iterated pullback arrows. -/
theorem pullbackArrowIso_inv_hom_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    iteratedToPullback G g ≫ pullbackToIterated G g = 𝟙 _ := sorry

/-- The canonical isomorphism from the restricted arrow space to the iterated fibre
product of the source and target pullback squares. -/
def pullbackArrowIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ≅ iteratedPullbackArrows G g where
  hom := pullbackToIterated G g
  inv := iteratedToPullback G g
  hom_inv_id := pullbackArrowIso_hom_inv_id G g
  inv_hom_id := pullbackArrowIso_inv_hom_id G g

/-- The `R`-projection through the upper fibre-product square agrees with the canonical
arrow projection. -/
theorem pullbackArrowIso_hom_upper_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst G.s g = pullbackArrow G g := sorry

/-- The `U'`-projection through the upper fibre-product square is the restricted source. -/
theorem pullbackArrowIso_hom_upper_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.snd G.s g = (G.toPreRelation.pullback g).s := sorry

/-- The `U'`-projection through the lower fibre-product square is the restricted target. -/
theorem pullbackArrowIso_hom_lower_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst g G.t = (G.toPreRelation.pullback g).t := sorry

/-- The `R`-projection through the lower fibre-product square agrees with the canonical
arrow projection. -/
theorem pullbackArrowIso_hom_lower_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.snd g G.t = pullbackArrow G g := sorry
end AlgebraicGeometry.GroupoidAlgebraicSpace
