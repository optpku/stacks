/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
import StacksCheckRecall

/-!
# Definition 31.23.1

The reusable meromorphic-function API is owned by
`ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction`.

@stack 01X2
-/

@[expose] public section

universe u

/-
Definition 31.23.1. For a locally ringed space `X`, the sheaf of meromorphic
functions is the sheaf associated to the total quotient presheaf, and a
meromorphic function on `X` is a global section of this sheaf.
-/
@[stacks 01X2] #check
  (AlgebraicGeometry.LocallyRingedSpace.meromorphicFunctionSheaf :
    (X : AlgebraicGeometry.LocallyRingedSpace.{u}) → TopCat.Sheaf CommRingCat X.toTopCat)

#check
  (AlgebraicGeometry.LocallyRingedSpace.meromorphicFunctions :
    AlgebraicGeometry.LocallyRingedSpace.{u} → CommRingCat.{u})
