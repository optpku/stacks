/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 74.21.1: for a scheme `S` and a property `P` of morphisms of algebraic
spaces over `S`, `P` is étale-smooth local on source-and-target when it is stable under
precomposition with étale maps, stable under smooth base change, and a morphism
`f : X ⟶ Y` has `P` if and only if every point of `|X|` lies under a commutative
square with smooth right vertical arrow, étale comparison `U ⟶ X ×_Y V`, and top
arrow of `P`. -/
@[stacks 0CFZ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget :
    {S : AlgebraicGeometry.Scheme.{u}} →
      CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S) → Prop)
