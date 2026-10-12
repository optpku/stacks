/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.Affine

@[expose] public section

universe u

namespace AlgebraicGeometry.IsClosedImmersion

/-- Closed immersions of schemes satisfy effective descent for fpqc coverings. -/
theorem satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.IsClosedImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc := sorry

end AlgebraicGeometry.IsClosedImmersion
