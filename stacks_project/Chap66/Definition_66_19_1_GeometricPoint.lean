/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
import StacksCheckRecall

universe u

/-!
# Geometric points of an algebraic space

@stack 0486

The public owner retains the actual geometric-point structure, postcomposition maps,
and comparisons with scheme geometric points.
-/

@[expose] public section

/- Definition 66.19.1 (1): a geometric point of an algebraic space `X` over a scheme `S` is a
morphism `Spec(k) ⟶ X` over `S` from the spectrum of an algebraically closed field. -/
@[stacks 0486 "(1) geometric point"]
#check (@AlgebraicGeometry.AlgebraicSpace.GeometricPoint :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))

/- Definition 66.19.1 (2): every geometric point has a corresponding image point in `|X|`. -/
@[stacks 0486 "(2) image point"]
#check (@AlgebraicGeometry.AlgebraicSpace.GeometricPoint.image :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X : AlgebraicGeometry.AlgebraicSpace S} →
      AlgebraicGeometry.AlgebraicSpace.GeometricPoint X →
        AlgebraicGeometry.AlgebraicSpace.Points X)

/- Definition 66.19.1 (2): a geometric point lies over `x` when its image is `x`. -/
@[stacks 0486 "(2) lying over a point"]
#check (@AlgebraicGeometry.AlgebraicSpace.GeometricPoint.liesOver :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X : AlgebraicGeometry.AlgebraicSpace S} →
      AlgebraicGeometry.AlgebraicSpace.GeometricPoint X →
        AlgebraicGeometry.AlgebraicSpace.Points X → Prop)

#check (@AlgebraicGeometry.AlgebraicSpace.GeometricPoint.of :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X : AlgebraicGeometry.AlgebraicSpace S} →
      (K : Type u) → [Field K] → [IsAlgClosed K] →
        (structureHom : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S) →
          (AlgebraicGeometry.AlgebraicSpace.ofOver
              (CategoryTheory.Over.mk structureHom) ⟶ X) →
            AlgebraicGeometry.AlgebraicSpace.GeometricPoint X)
#check (@AlgebraicGeometry.AlgebraicSpace.GeometricPoint.map :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X Y : AlgebraicGeometry.AlgebraicSpace S} →
      AlgebraicGeometry.AlgebraicSpace.GeometricPoint X →
        (X ⟶ Y) → AlgebraicGeometry.AlgebraicSpace.GeometricPoint Y)
#check (@AlgebraicGeometry.AlgebraicSpace.GeometricPoint.ofScheme :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {U : CategoryTheory.Over S} →
      AlgebraicGeometry.Scheme.GeometricPoint U.left →
        AlgebraicGeometry.AlgebraicSpace.GeometricPoint
          (AlgebraicGeometry.AlgebraicSpace.ofOver U))
#check (@AlgebraicGeometry.AlgebraicSpace.GeometricPoint.toScheme :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {U : CategoryTheory.Over S} →
      AlgebraicGeometry.AlgebraicSpace.GeometricPoint
          (AlgebraicGeometry.AlgebraicSpace.ofOver U) →
        AlgebraicGeometry.Scheme.GeometricPoint U.left)
