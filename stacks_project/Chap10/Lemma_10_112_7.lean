/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.GoingDown
import StacksCheckRecall

/-!
# Going-Down Local Dimension Formula

@stack 00ON
-/

@[expose] public section

/- Lemma 10.112.7 (Stacks tag `00ON`): for primes `q` over `p` in a
Noetherian going-down map, `dim S_q = dim R_p + dim (S_q / pS_q)`. -/
@[stacks 00ON]
#check @Algebra.GoingDown.krullDim_eq_add_quotientDim_of_liesOver

/- Canonical pointwise and local-fiber presentations of the same formula. -/
@[stacks 00ON "pointwise quotient-dimension formula"]
#check @Algebra.GoingDown.krullDim_eq_add_quotientDim

@[stacks 00ON "local fiber-dimension formula"]
#check @Algebra.GoingDown.krullDim_eq_add_fiberDim

@[stacks 00ON "local fiber-dimension formula with lying-over"]
#check @Algebra.GoingDown.krullDim_eq_add_fiberDim_of_liesOver
