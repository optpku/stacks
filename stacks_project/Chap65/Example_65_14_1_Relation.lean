module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-!
# The affine-line involution relation

The pre-relation on the affine line is defined by the disjoint union of its diagonal
and the graph of negation on the punctured affine line.
-/

@[expose] public section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.preRelation :
    ∀ (k : Type u) [Field k], AlgebraicGeometry.Scheme.PreRelation
      (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.cover k))
