/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedExtension

open AlgebraicGeometry AlgebraicGeometry.Scheme.FunctionFieldExtension
universe u

#check (maximalUnramifiedExtension :
  (X : Scheme.{u}) → [IsIntegral X] → X.isNormal →
    IntermediateField X.functionField (SeparableClosure X.functionField))
