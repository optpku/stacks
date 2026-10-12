/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Pullback of relations on schemes

This module defines base change of pre-relations and relations in the slice category of schemes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace PreRelation

/-- Pull a pre-relation on `U` back along a morphism `g : U' ⟶ U` over the base. -/
def pullback {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U) (g : U' ⟶ U) :
    PreRelation U' :=
  (Over.pullback (prod.map g g)).obj P

/-- The source of a pulled-back pre-relation is the categorical pullback of its source. -/
theorem pullback_left {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) :
    (P.pullback g).left = Limits.pullback P.hom (prod.map g g) := sorry

/-- The defining map of a pulled-back pre-relation is the second pullback projection. -/
theorem pullback_hom {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) :
    (P.pullback g).hom = Limits.pullback.snd P.hom (prod.map g g) := sorry

/-- Pullback relates two points exactly when their images are related by the original
pre-relation. -/
theorem pullback_pointRel_iff {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) (T : Over S) (x y : T ⟶ U') :
    (P.pullback g).pointRel T x y ↔ P.pointRel T (x ≫ g) (y ≫ g) := sorry

/-- Pulling back a pre-relation with monic defining map preserves monicity. -/
instance instMonoHomPullback {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) [Mono P.hom] : Mono (P.pullback g).hom := sorry

namespace IsPreEquivalence

/-- Pullback preserves pointwise pre-equivalence. -/
theorem pullback {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    (hP : P.IsPreEquivalence) (g : U' ⟶ U) : (P.pullback g).IsPreEquivalence := sorry

end IsPreEquivalence

/-- Pullback preserves internal equivalence relations. -/
instance instIsEquivalenceRelationPullback {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s] :
    IsEquivalenceRelation (P.pullback g).t (P.pullback g).s := sorry

end PreRelation

namespace Relation

/-- Pull a relation on `U` back along a morphism `g : U' ⟶ U` over the base. -/
def pullback {S : Scheme.{u}} {U U' : Over S} (Q : Relation U) (g : U' ⟶ U) :
    Relation U' :=
  (MonoOver.pullback (prod.map g g)).obj Q

/-- Forgetting monicity after pulling back a relation gives the pulled-back pre-relation. -/
theorem pullback_toPreRelation {S : Scheme.{u}} {U U' : Over S} (Q : Relation U)
    (g : U' ⟶ U) :
    (Q.pullback g).toPreRelation = Q.toPreRelation.pullback g := sorry

end Relation

end AlgebraicGeometry.Scheme
