/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Presentation.Jacobian.LeftInverse

@[expose] public section

/- Lemma 16.2.4 (1): the Jacobian-minor condition in `A` produces an
`A`-linear left inverse up to the chosen scalar. -/
@[stacks 07ET]
#check @Algebra.Presentation.Jacobian.exists_leftInverse

/- Lemma 16.2.4 (2): a target-side scalar left inverse places the
corresponding scalar power in the Jacobian minor ideal. -/
@[stacks 07ET]
#check @Algebra.Presentation.Jacobian.leftInverse_pow_mem
