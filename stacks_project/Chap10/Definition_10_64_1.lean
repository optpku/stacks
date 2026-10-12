/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.SymbolicPower
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.64.1

This chapter entry is a source-facing recall of the reusable symbolic-power
owner in `ReasLib.RingTheory.Ideal.SymbolicPower`.

@stack 0313
-/

/- Definition 10.64.1 (Tag 0313): the `n`th symbolic power of a prime ideal is
the contraction of its `n`th power from the localization at that prime. -/
@[stacks 0313]
#check @Ideal.symbolicPower

/- The zeroth symbolic power is the unit ideal. -/
@[stacks 0313 "zeroth symbolic power"]
#check @Ideal.symbolicPower_zero

/- Definition 10.64.1 in its quotient-kernel form. -/
@[stacks 0313]
#check @Ideal.symbolicPower_eq_ker_quotient_map_pow

/- Positive symbolic powers are primary and have radical equal to the original
prime ideal. -/
@[stacks 0313 "primary symbolic powers"]
#check @Ideal.symbolicPower_isPrimary
@[stacks 0313 "radical of a symbolic power"]
#check @Ideal.radical_symbolicPower
