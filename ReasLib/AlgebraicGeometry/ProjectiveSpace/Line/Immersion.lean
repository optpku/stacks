module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
import Mathlib.Tactic.CrossRefAttribute

/-!
# Immersions of the projective line

This leaf isolates the obstruction to immersing a projective line into an affine scheme from the
core construction of the projective line.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveLine

variable (k : Type u) [Field k]

/-- There is no immersion from the projective line over a field into an affine scheme. -/
@[stacks 01KX "projective line has no immersion into an affine scheme"]
theorem no_immersion_to_affine (Y : Scheme.{u}) [IsAffine Y] (f : scheme k ⟶ Y) :
    ¬ IsImmersion f := sorry

end AlgebraicGeometry.ProjectiveLine
