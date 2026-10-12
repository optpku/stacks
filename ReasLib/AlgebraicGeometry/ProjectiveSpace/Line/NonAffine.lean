/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveLine

/-- The structure morphism of the projective line over a field is not affine. -/
theorem not_isAffineHom_toSpec (k : Type u) [Field k] :
    ¬ IsAffineHom (ProjectiveLine.toSpec k) := sorry

end AlgebraicGeometry.ProjectiveLine
