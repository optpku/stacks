/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ResidueGalois
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 59.56.1 (1): the separable closure of the residue field inside
the source field of a geometric point. -/
@[stacks 03QX] #check (AlgebraicGeometry.Scheme.GeometricPoint.separableClosure :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (s : AlgebraicGeometry.Scheme.GeometricPoint S) →
      IntermediateField (S.residueField s.toFieldValuedPoint.image) s.K)

/- Definition 59.56.1 (2): the absolute Galois group of the residue field is
Gal of the point-specific separable closure. -/
@[stacks 03QX] #check (AlgebraicGeometry.Scheme.GeometricPoint.absoluteGaloisGroup :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (s : AlgebraicGeometry.Scheme.GeometricPoint S) → Type u)

/- Definition 59.56.1 (3): a geometric point is algebraic when its source field
is an algebraic closure of the residue field at its image. -/
@[stacks 03QX] #check (AlgebraicGeometry.Scheme.GeometricPoint.IsAlgebraic :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.Scheme.GeometricPoint S → Prop)
