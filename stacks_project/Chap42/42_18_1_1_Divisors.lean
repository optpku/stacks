/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Divisor

universe u

#check (AlgebraicGeometry.ProjectiveLine.Relative.zeroDivisor :
  (S : AlgebraicGeometry.Scheme.{u}) →
    (AlgebraicGeometry.ProjectiveSpace 1 S).IdealSheafData)

#check (AlgebraicGeometry.ProjectiveLine.Relative.infinityDivisor :
  (S : AlgebraicGeometry.Scheme.{u}) →
    (AlgebraicGeometry.ProjectiveSpace 1 S).IdealSheafData)
