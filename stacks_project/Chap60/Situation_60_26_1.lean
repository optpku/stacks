/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Situation_60_7_5
public import ReasLib.RingTheory.DividedPowers.Category
import ReasLib.AlgebraicGeometry.Crystalline.Frobenius
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

section

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A : DividedPowerRing.{u})

/- Situation 60.26.1: A prime-local crystalline base presented by a divided-power
ring `A`, with `p ∈ A.ideal` and a chosen divided-power endomorphism lifting the
`p`-power map modulo `pA`. -/
@[stacks 07N2] #check
  (AlgebraicGeometry.Scheme.Crystalline.FrobeniusBase p A : Type (u + 1))

end
