/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic.Moduli
import StacksCheckRecall

universe u

/- Exercise 111.47.2: the moduli of hyperelliptic curves of genus `g` has number
of moduli `2 * g - 1` over an algebraically closed field when `2 ≤ g`. -/
@[stacks 0EGQ] #check
  (AlgebraicGeometry.Curve.Hyperelliptic.Moduli.hasNumberOfModuli_hyperelliptic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}, 2 ≤ g →
      AlgebraicGeometry.Curve.Hyperelliptic.Moduli.HasNumberOfModuli k g (2 * g - 1))
