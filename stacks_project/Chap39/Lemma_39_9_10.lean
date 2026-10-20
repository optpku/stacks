/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj AbelianVariety

universe u

/- Lemma 39.9.10: For an abelian variety `A` over a field of prime characteristic `p`,
the fibre of multiplication by `p` over the identity point has at most `p ^ dimension A`
distinct points. -/
@[stacks 0C0Y] #check
  (AlgebraicGeometry.AbelianVariety.mulBy_fiber_zero_encard_le :
    {k : Type u} → [Field k] → (p : ℕ) → [Fact p.Prime] → [CharP k p] →
      (A : SchemeOverField k) → [GrpObj A] → [AbelianVariety A] →
        (([p]ₐ A).pointsOver (η[A].left (IsLocalRing.closedPoint k))).encard ≤
          p ^ AlgebraicGeometry.AbelianVariety.dimension A)
