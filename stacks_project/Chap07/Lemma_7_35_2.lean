module

public import ReasLib.CategoryTheory.Sites.Point.OverClassification
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.35.2

The reusable owner is the point-over-slice API in ReasLib.  Mathlib models
equality of geometric points by isomorphism, so the source correspondence is
recorded here as the classification of points lying over `p` up to point
isomorphism; a chosen lying-over identification is deliberately not discarded
inside a false uniqueness claim.
-/

@[expose] public section

/- Lemma 7.35.2 (04H3): elements of `p.fiber.obj U` classify, up to point isomorphism, the
points of `(C / U, J.over U)` lying over `p`. -/
@[stacks 04H3] #check @CategoryTheory.GrothendieckTopology.Point.Over.liesOver_iff_exists_isomorphic_over

@[stacks 04H3] #check @CategoryTheory.GrothendieckTopology.Point.Over.over_liesOver
