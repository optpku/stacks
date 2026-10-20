/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.29.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `f` is flat, proper, and of finite presentation, then the set
`E = geometricallyReducedFiberLocus f` of points of `|Y|` at which the fibre of `f`
is geometrically reduced is open in `|Y|`. -/
@[stacks 0E0C]
#check (AlgebraicGeometry.AlgebraicSpace.isOpen_geometricallyReducedFiberLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [Flat f] → [Proper f] → [FinitePresentation f] →
      IsOpen (geometricallyReducedFiberLocus f))
