/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EquivalenceRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Étale equivalence relations on algebraic spaces

This module records the property of a pair of parallel arrows in `Over B` being
an étale equivalence relation of algebraic spaces over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale equivalence relation on `U` over `B` is an equivalence relation
whose two projections to `U` are étale. -/
@[mk_iff]
class IsEtaleEquivalenceRelation {S : Scheme.{u}} {B : AlgebraicSpace S}
    {R U : Over B} (t s : R ⟶ U) : Prop where
  /-- The two projections form an internal equivalence relation. -/
  isEquivalenceRelation : IsEquivalenceRelation t s
  /-- The first projection is étale. -/
  etale_t : Etale t.left
  /-- The second projection is étale. -/
  etale_s : Etale s.left

/-- An equivalence relation with étale projections is an étale equivalence
relation. -/
instance instIsEtaleEquivalenceRelation {S : Scheme.{u}} {B : AlgebraicSpace S}
    {R U : Over B} (t s : R ⟶ U) [IsEquivalenceRelation t s] [Etale t.left]
    [Etale s.left] : IsEtaleEquivalenceRelation t s where
  isEquivalenceRelation := inferInstance
  etale_t := inferInstance
  etale_s := inferInstance

end AlgebraicGeometry.AlgebraicSpace
