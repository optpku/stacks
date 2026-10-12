/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback

/-!
# Étale stability of restricted pre-relations

This module records that étale projections, and étale equivalence relations, remain étale after
restriction along an étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Restricting an étale target projection along an étale morphism remains étale. -/
instance etale_pullback_t {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) [Etale P.t.left] [Etale g.left] : Etale (P.pullback g).t.left := sorry

/-- Restricting an étale source projection along an étale morphism remains étale. -/
instance etale_pullback_s {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) [Etale P.s.left] [Etale g.left] : Etale (P.pullback g).s.left := sorry

/-- The restriction of an étale equivalence relation along an étale morphism is an étale
equivalence relation. -/
instance instIsEtaleEquivalenceRelationPullback {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) [P.IsEtaleEquivalenceRelation] [Etale g.left] :
    (P.pullback g).IsEtaleEquivalenceRelation := sorry

/-- Restriction along an étale morphism preserves the equivalence relation and both étale
projections. -/
theorem isEtaleEquivalenceRelation_pullback_spec {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) [P.IsEtaleEquivalenceRelation] [Etale g.left] :
    IsEquivalenceRelation (P.pullback g).t (P.pullback g).s ∧
      Etale (P.pullback g).t.left ∧ Etale (P.pullback g).s.left := sorry

end AlgebraicGeometry.Scheme.PreRelation
