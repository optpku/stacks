/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.HenselianFraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Order
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyFinite
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 72.6.6 (1): The prime divisors where a rational unit fails to belong to
the henselian local ring at their generic points are locally finite. -/
@[stacks 0ENN] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyFinite_primeDivisors_not_mem_henselianLocalRing :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
      (f : (RationalFunction X)ˣ),
      LocallyFinite fun Z : PrimeDivisor X ↦
        {x | ¬ Z.mem_henselianLocalRing (f : RationalFunction X) ∧ x ∈ Z.pointsSet})

/- Lemma 72.6.6 (2): The prime divisors along which a rational unit has nonzero
order are locally finite. -/
@[stacks 0ENN] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyFinite_primeDivisors_ord_ne_zero :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
      (f : (RationalFunction X)ˣ),
      LocallyFinite fun Z : PrimeDivisor X ↦
        if Z.ord f = 0 then (∅ : Set (Points X)) else Z.pointsSet)
