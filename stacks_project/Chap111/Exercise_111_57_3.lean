/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.PlaneCurve
import StacksCheckRecall

/-! # Exercise 111.57.3 compatibility entry point -/

@[expose] public section

open scoped AlgebraicGeometry
open AlgebraicGeometry

/- Exercise 111.57.3 (1): a plane curve meeting every line. -/
@[stacks 0AAP] #check
  (AlgebraicGeometry.AffineSpace.graphSquare_meets_every_line :
    AlgebraicGeometry.AffineSpace.IsPlaneCurve
        AlgebraicGeometry.AffineSpace.graphSquare ∧
      ∀ I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData,
        AlgebraicGeometry.AffineSpace.IsLine I →
          AlgebraicGeometry.AffineSpace.Meets
            AlgebraicGeometry.AffineSpace.graphSquare I)

/- Exercise 111.57.3 (2): a plane curve meeting every line and quadric. -/
@[stacks 0AAP] #check
  (AlgebraicGeometry.AffineSpace.graphCube_meets_every_line_and_quadric :
    AlgebraicGeometry.AffineSpace.IsPlaneCurve
        AlgebraicGeometry.AffineSpace.graphCube ∧
      ∀ I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData,
        (AlgebraicGeometry.AffineSpace.IsLine I ∨
          AlgebraicGeometry.AffineSpace.IsQuadric I) →
          AlgebraicGeometry.AffineSpace.Meets
            AlgebraicGeometry.AffineSpace.graphCube I)

/- Exercise 111.57.3 (3): every plane curve has a disjoint plane curve. -/
@[stacks 0AAP] #check
  (AlgebraicGeometry.AffineSpace.exists_disjoint_planeCurve :
    ∀ (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData),
      AlgebraicGeometry.AffineSpace.IsPlaneCurve I →
        ∃ J : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData,
          AlgebraicGeometry.AffineSpace.IsPlaneCurve J ∧
            I.support ⊓ J.support = ⊥)
