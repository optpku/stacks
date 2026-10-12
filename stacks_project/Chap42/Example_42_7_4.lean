/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.DimensionFunction

universe u

/- Example 42.7.4 (1): a Cohen–Macaulay scheme is universally catenary. -/
@[stacks 0F91] #check
  (AlgebraicGeometry.instUniversallyCatenaryOfCohenMacaulay :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.CohenMacaulay S],
      AlgebraicGeometry.UniversallyCatenary S)

/- Example 42.7.4 (2): its dimension function is the negative dimension of each local ring. -/
@[stacks 0F91] #check
  (AlgebraicGeometry.Scheme.CohenMacaulay.dimensionFunction_apply :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.CohenMacaulay S] (s : S),
      AlgebraicGeometry.Scheme.CohenMacaulay.dimensionFunction S s =
        -(((ringKrullDim (S.presheaf.stalk s)).unbotD 0).toNat : ℤ))

/- Example 42.7.4 (3): the negative local-ring dimension is a dimension function. -/
@[stacks 0F91] #check
  (AlgebraicGeometry.Scheme.CohenMacaulay.instIsDimensionFunction :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.CohenMacaulay S],
      IsDimensionFunction (AlgebraicGeometry.Scheme.CohenMacaulay.dimensionFunction S))
