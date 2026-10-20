/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ResidueGalois

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.GeometricPoint.separableClosure :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (s : AlgebraicGeometry.Scheme.GeometricPoint S) →
      IntermediateField (S.residueField s.toFieldValuedPoint.image) s.K)
