/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham
import StacksCheckRecall

@[expose] public section

/-!
# Equation 10.132.0.1

@stack 0FKG

The de Rham differential sends `b₀ db₁ ∧ ... ∧ dbₚ` to
`db₀ ∧ db₁ ∧ ... ∧ dbₚ`.
-/

/- 10.132.0.1: the canonical Kähler de Rham differential satisfies the displayed formula in
every degree. -/
@[stacks 0FKG]
#check @KaehlerDifferential.DeRham.d_basic

/- The same equation is the uniform formula field for any abstract de Rham differential family. -/
@[stacks 0FKG "generic de Rham formula"]
#check @DifferentialOperator.DeRham.SatisfiesFormula.basic
