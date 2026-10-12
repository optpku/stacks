/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

/-!
# Étale equivalence relations

This module records the property of a pre-relation on a scheme over a base being an étale
equivalence relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- An étale equivalence relation on `U` over `S` is an equivalence relation whose two projections
to `U` are étale. -/
@[mk_iff]
class IsEtaleEquivalenceRelation {S : Scheme.{u}} {U : Over S} (P : PreRelation U) : Prop where
  /-- The two projections form an internal equivalence relation. -/
  isEquivalenceRelation : IsEquivalenceRelation P.t P.s
  /-- The first projection is étale. -/
  etale_t : Etale P.t.left
  /-- The second projection is étale. -/
  etale_s : Etale P.s.left

/-- An equivalence relation with étale projections is an étale equivalence relation. -/
instance instIsEtaleEquivalenceRelation {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] [Etale P.t.left] [Etale P.s.left] :
    P.IsEtaleEquivalenceRelation where
  isEquivalenceRelation := inferInstance
  etale_t := inferInstance
  etale_s := inferInstance

end AlgebraicGeometry.Scheme.PreRelation
