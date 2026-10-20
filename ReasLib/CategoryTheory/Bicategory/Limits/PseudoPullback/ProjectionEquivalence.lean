module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence.Computations

/-!
# Equivalences of pseudopullback projections

This compatibility import assembles the directional projection-equivalence API. The left leaf
owns the standard left-equivalence cone and second projection; the right leaf derives the
symmetric statements by the readable pseudopullback swap; `Computations` adds the oriented
`iso.hom`/`iso.inv` readouts. Directional consumers should import the smallest leaf that
contains their required projection or computation.
-/
