/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation

/-!
# Pre-relations of groupoids in algebraic spaces

This module records the pre-relation underlying a groupoid in algebraic spaces over a base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

/-- Forget a groupoid in algebraic spaces to its underlying pre-relation, with defining
map `(t, s)`. -/
def toPreRelation {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.PreRelation G.U :=
  AlgebraicSpace.PreRelation.ofHom (prod.lift G.t G.s)

/-- The defining map of the underlying pre-relation is the product lift `(t, s)`. -/
theorem toPreRelation_hom {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.hom = prod.lift G.t G.s := sorry

/-- The target projection of the underlying pre-relation is the target map. -/
theorem toPreRelation_t {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.t = G.t := sorry

/-- The source projection of the underlying pre-relation is the source map. -/
theorem toPreRelation_s {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.s = G.s := sorry

/-- The morphism `j = (t, s)` of a groupoid in algebraic spaces over `B` is a
pre-equivalence relation. -/
theorem toPreRelation_isPreEquivalence {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.IsPreEquivalence := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
