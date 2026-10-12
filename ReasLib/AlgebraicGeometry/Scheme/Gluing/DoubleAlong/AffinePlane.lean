/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.AffinePlane
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# The affine plane with doubled origin

This file contains only the dimension-two bridge between the general doubled-origin affine-space
construction and the canonical punctured affine plane.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.DoubledOrigin

variable (k : Type u) [CommRing k]

/-- In dimension two, the open used for doubled-origin gluing is the canonical punctured affine
plane. -/
@[stacks 01JD "punctured affine plane overlap"]
theorem puncturedOpen_two_eq_puncturedAffinePlane :
    puncturedOpen k 2 = PuncturedAffinePlane.puncturedOpen k := sorry

end AlgebraicGeometry.DoubledOrigin
