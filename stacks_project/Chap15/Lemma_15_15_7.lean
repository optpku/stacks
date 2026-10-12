/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Dual.FiniteFree
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.15.7

@stack 0EWY
-/

/- Lemma 15.15.7 (`0EWY`): an injective endomorphism of `R^n` has cokernel with zero
`R`-linear dual. -/
@[stacks 0EWY]
#check @LinearMap.quotient_range_dual_eq_zero_of_injective_fin

#check @LinearMap.range_dualAnnihilator_eq_bot_of_injective
#check @LinearMap.quotient_range_dual_subsingleton_of_injective
#check @LinearMap.quotient_range_dual_eq_zero_of_injective
