/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Pullback

/-!
# Blowing up a decent algebraic space at a closed point

A closed point of a decent algebraic space is represented by the residue-field
closed immersion `fromSpecResidueField`. The blowup at that point is the blowup
along the corresponding closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofClosedPoint :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)), ClosedSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofClosedPoint_ι :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)),
      (ClosedSubspace.ofClosedPoint x hx).ι = X.fromSpecResidueField x)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofClosedPoint_spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)),
      IsClosedImmersion (ClosedSubspace.ofClosedPoint x hx).ι ∧
        (ClosedSubspace.ofClosedPoint x hx).ι = X.fromSpecResidueField x ∧
        Points.mk (FieldValuedPoint.residuePoint x) = x)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.atPoint :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)), Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.atPoint_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)),
      Blowup.atPoint x hx = Blowup.along (ClosedSubspace.ofClosedPoint x hx))
