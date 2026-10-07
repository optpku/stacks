module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction

/-!
# Fibre-product presentation of restricted groupoid arrows

This module identifies the arrow scheme of a restricted groupoid scheme with the corresponding
iterated fibre product and records its projection formulas.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The arrow scheme in the iterated fibre-product presentation of a restriction. -/
abbrev iteratedPullbackArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) : Over S :=
  Limits.pullback (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t)

/-- The restricted arrow scheme maps canonically to `R ×_{s, U} U'`. -/
def pullbackToSourceSquare {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ Limits.pullback G.s g :=
  Limits.pullback.lift (pullbackArrow G g) (G.toPreRelation.pullback g).s
    (pullbackArrow_s G g)

/-- The two maps defining the canonical morphism to `U' ×_{U, t} R` commute. -/
theorem pullbackToTargetSquare_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).t ≫ g = pullbackArrow G g ≫ G.t := sorry

/-- The restricted arrow scheme maps canonically to `U' ×_{U, t} R`. -/
def pullbackToTargetSquare {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ Limits.pullback g G.t :=
  Limits.pullback.lift (G.toPreRelation.pullback g).t (pullbackArrow G g)
    (pullbackToTargetSquare_condition G g)

/-- The two square maps from the restricted arrow scheme have the same arrow projection. -/
theorem pullbackToIterated_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    pullbackToSourceSquare G g ≫ Limits.pullback.fst G.s g =
      pullbackToTargetSquare G g ≫ Limits.pullback.snd g G.t := sorry

/-- The canonical map from the single-pullback arrow scheme to the displayed iterated
fibre product. -/
def pullbackToIterated {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ⟶ iteratedPullbackArrows G g :=
  Limits.pullback.lift (pullbackToSourceSquare G g) (pullbackToTargetSquare G g)
    (pullbackToIterated_condition G g)

/-- The arrow and endpoint projections from the displayed iterated fibre product satisfy
the single-pullback compatibility equation. -/
theorem iteratedToPullback_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst G.s g) ≫ G.toPreRelation.hom =
      prod.lift
          (Limits.pullback.snd (Limits.pullback.fst G.s g)
              (Limits.pullback.snd g G.t) ≫ Limits.pullback.fst g G.t)
          (Limits.pullback.fst (Limits.pullback.fst G.s g)
              (Limits.pullback.snd g G.t) ≫ Limits.pullback.snd G.s g) ≫
        prod.map g g := sorry

/-- The canonical map from the displayed iterated fibre product to the single-pullback
arrow scheme. -/
def iteratedToPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
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

/-- The canonical isomorphism from the restricted arrow scheme to the iterated fibre
product of the source and target pullback squares. -/
def pullbackArrowIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.toPreRelation.pullback g).left ≅ iteratedPullbackArrows G g where
  hom := pullbackToIterated G g
  inv := iteratedToPullback G g
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The `R`-projection through the upper fibre-product square agrees with the canonical
arrow projection. -/
theorem pullbackArrowIso_hom_upper_fst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst G.s g = pullbackArrow G g := sorry

/-- The `U'`-projection through the upper fibre-product square is the restricted source. -/
theorem pullbackArrowIso_hom_upper_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.snd G.s g = (G.toPreRelation.pullback g).s := sorry

/-- The `U'`-projection through the lower fibre-product square is the restricted target. -/
theorem pullbackArrowIso_hom_lower_fst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.fst g G.t = (G.toPreRelation.pullback g).t := sorry

/-- The `R`-projection through the lower fibre-product square agrees with the canonical
arrow projection. -/
theorem pullbackArrowIso_hom_lower_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackArrowIso G g).hom ≫
        Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
      Limits.pullback.snd g G.t = pullbackArrow G g := sorry

end AlgebraicGeometry.GroupoidScheme

