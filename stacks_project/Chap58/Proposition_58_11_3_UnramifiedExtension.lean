module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedExtension

open AlgebraicGeometry AlgebraicGeometry.Scheme.FunctionFieldExtension
universe u

#check (maximalUnramifiedExtension :
  (X : Scheme.{u}) → [IsIntegral X] → X.isNormal →
    IntermediateField X.functionField (SeparableClosure X.functionField))
