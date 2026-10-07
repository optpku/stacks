module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Pullback of pre-relations on algebraic spaces

This module defines base change of pre-relations in the slice category of algebraic spaces over a
base algebraic space.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PreRelation

/-- Pull a pre-relation on `U` back along a morphism `g : U' ⟶ U` over the base. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} [HasPullbacks (AlgebraicSpace S)]
    {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) : PreRelation U' :=
  (Over.pullback (prod.map g g)).obj P

/-- The source of a pulled-back pre-relation is the categorical pullback of its source. -/
theorem pullback_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    [HasPullbacks (AlgebraicSpace S)] {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.pullback g).left = Limits.pullback P.hom (prod.map g g) := sorry

/-- The defining map of a pulled-back pre-relation is the second pullback projection. -/
theorem pullback_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    [HasPullbacks (AlgebraicSpace S)] {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.pullback g).hom = Limits.pullback.snd P.hom (prod.map g g) := sorry

/-- Pullback relates two points exactly when their images are related by the original
pre-relation. -/
theorem pullback_pointRel_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    [HasPullbacks (AlgebraicSpace S)] {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) {T : Over S} (τ : ofOver T ⟶ B)
    (x y : Over.mk τ ⟶ U') :
    (P.pullback g).pointRel (Over.mk τ) x y ↔
      P.pointRel (Over.mk τ) (x ≫ g) (y ≫ g) := sorry

/-- Pulling back a pre-relation with monic defining map preserves monicity. -/
instance instMonoHomPullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    [HasPullbacks (AlgebraicSpace S)] {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) [Mono P.hom] : Mono (P.pullback g).hom := sorry

namespace IsPreEquivalence

/-- Pullback preserves pointwise pre-equivalence. -/
theorem pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    [HasPullbacks (AlgebraicSpace S)] {U U' : Over B}
    {P : PreRelation U} (hP : P.IsPreEquivalence) (g : U' ⟶ U) :
    (P.pullback g).IsPreEquivalence := sorry

end IsPreEquivalence

/-- Pullback preserves internal equivalence relations. -/
instance instIsEquivalenceRelationPullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    [HasPullbacks (AlgebraicSpace S)] {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U)
    [IsEquivalenceRelation P.t P.s] :
    IsEquivalenceRelation (P.pullback g).t (P.pullback g).s := sorry

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
