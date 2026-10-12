/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.ProjSpec

/- 37.51.0.1: The integral and nonnegative relative spectra of the twists on `P = Proj(A)`
form a commutative two-square diagram with `U`, `L`, `X = Spec(A)`, and `Z = Spec(A₀)`. -/
@[stacks 0EKG] #check (AlgebraicGeometry.ProjSpec.diagram :
  (C : AlgebraicGeometry.ProjSpec.Construction) → AlgebraicGeometry.ProjSpec.Diagram C)
