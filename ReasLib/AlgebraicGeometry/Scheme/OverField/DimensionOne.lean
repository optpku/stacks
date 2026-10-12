/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.AffineCover
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.DimensionZero
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.AffineOrProjective

/-!
# Affineness of one-dimensional schemes over a field

This file records an affineness criterion for algebraic schemes of dimension at most one.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Algebraic

variable {k : Type u} [Field k]

/-- A separated algebraic scheme over a field of dimension at most one is affine if none of its
one-dimensional reduced irreducible components is proper over the field. -/
theorem isAffine_of_dimLEOne_of_nonproper_irreducibleComponents
    (X : SchemeOverField k) [Algebraic X] [IsSeparated X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hnonproper :
      ∀ Z : irreducibleComponents X.left,
        topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1 →
          ¬ IsProper (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)) :
    IsAffine X.left := sorry

end AlgebraicGeometry.Algebraic
