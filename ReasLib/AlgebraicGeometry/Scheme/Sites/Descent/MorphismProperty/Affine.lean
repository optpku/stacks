/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.AffineCriterion

@[expose] public section

universe u

namespace AlgebraicGeometry.IsAffineHom

/-- Affine scheme morphisms satisfy effective descent for fpqc coverings. -/
theorem satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.IsAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc := sorry

end AlgebraicGeometry.IsAffineHom
