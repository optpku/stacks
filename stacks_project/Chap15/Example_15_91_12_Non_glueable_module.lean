/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion.Counterexample

import StacksCheckRecall

/-!
# A non-glueable module

The reusable algebraic core of the smooth-germ example is owned by
`LocalizedModule.Away.BeauvilleLaszlo.quotient_notGlueableAlong_principalAdicCompletion_of_witness`.
For the source specialization, `f(x) = x`, `φ(x) = exp(-1 / x ^ 2)`, and `ψ = φ / f`.

@stack 0BNY
-/

-- The explicit quotient class in the `f`-primary component.
@[stacks 0BNY "quotient torsion witness"]
#check @LocalizedModule.Away.BeauvilleLaszlo.quotientPrimaryComponentWitness

-- Its nonvanishing is exactly nonvanishing of the underlying quotient class.
@[stacks 0BNY "nonvanishing quotient torsion witness"]
#check @LocalizedModule.Away.BeauvilleLaszlo.quotientPrimaryComponentWitness_ne_zero

-- Example 15.91.12 (Non glueable module): the completion-kernel witness obstructs glueability.
@[stacks 0BNY "Example 15.91.12 (Non glueable module)"]
#check @LocalizedModule.Away.BeauvilleLaszlo.quotient_notGlueableAlong_principalAdicCompletion_of_witness
