/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.IntegerConic
import StacksCheckRecall

@[expose] public section

/- Exercise 111.29.1 (1): there is no ring map from the explicit finite-type
`ℤ`-algebra `CoordinateRing` to `ℚ`. -/
@[stacks 02EO] #check
  (AlgebraicGeometry.IntegerConic.not_exists_ringHom_rat :
    ¬ Nonempty
      (AlgebraicGeometry.IntegerConic.CoordinateRing →+* ℚ))

/- Exercise 111.29.1 (2): for every prime `p` there is a maximal ideal `m`
whose residue ring is isomorphic to `ZMod p`. -/
@[stacks 02EO] #check
  (AlgebraicGeometry.IntegerConic.exists_maximalIdeal_residueEquiv_zmod :
    (p : ℕ) → [Fact p.Prime] →
      ∃ m : Ideal AlgebraicGeometry.IntegerConic.CoordinateRing, m.IsMaximal ∧
        Nonempty
          ((AlgebraicGeometry.IntegerConic.CoordinateRing ⧸ m) ≃+* ZMod p))
