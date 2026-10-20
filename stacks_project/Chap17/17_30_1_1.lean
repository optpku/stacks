/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Algebraic.DeRham
import StacksCheckRecall

@[expose] public section

/- Equation 17.30.1.1 (0FKN): the de Rham differential sends
`b₀ db₁ ∧ ... ∧ dbₚ` to `db₀ ∧ db₁ ∧ ... ∧ dbₚ`. -/
@[stacks 0FKN]
#check @TopCat.Sheaf.DeRham.d_basic
