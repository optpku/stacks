/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GoldenInteger
import StacksCheckRecall

@[expose] public section

/- Exercise 111.34.7: the golden-integer scheme is a closed subscheme of the
localized affine line over the integers. -/
@[stacks 0299] #check
  (AlgebraicGeometry.GoldenIntegerQuasiSection.instIsClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      AlgebraicGeometry.GoldenIntegerQuasiSection.closedImmersion)
