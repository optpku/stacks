/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedExtension

open AlgebraicGeometry AlgebraicGeometry.Scheme.FunctionFieldExtension
universe u

#check (maximalUnramifiedExtension :
  (X : Scheme.{u}) → [IsIntegral X] → X.isNormal →
    IntermediateField X.functionField (SeparableClosure X.functionField))
