/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LinearSystem.PointSum
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField AlgebraicGeometry.LinearSystem
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Exercise 111.46.4: the closed incidence subscheme parametrizes linear
combinations vanishing on the point-sum divisor, including repeated points. -/
@[stacks 0EGC] #check (AlgebraicGeometry.LinearSystem.exists_vanishingOnPointSumLocus :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    (r : ℕ) (hr : 1 ≤ r),
    ∃ Z : (product (tensorPower X r) n).IdealSheafData,
      ∀ {v : Fin (n + 1) → k} (hv : v ≠ 0)
        {x : Fin r → X.left} (hx : ∀ i, x i ∈ closedPoints X.left)
        {z : product (tensorPower X r) n}
        (hz : z ∈ closedPoints (product (tensorPower X r) n)),
        fst (tensorPower X r) n z =
            ProjectiveSpace.homOf (RingHom.id k) hv (IsLocalRing.closedPoint k) →
          (∀ i, (coord X r i).left.base (snd (tensorPower X r) n z) = x i) →
            (z ∈ Z.support ↔
              Scheme.Modules.vanishesOnDivisor
                (linearCombination X L n s v) (Curve.pointSumDivisor X x hx)))
