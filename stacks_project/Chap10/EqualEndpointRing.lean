/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.Equalizer
import StacksCheckRecall

/-!
# Equal-endpoint polynomial rings

@stack 00F1
@stack 00JG

The equal-endpoint polynomial ring is the canonical `Subalgebra` `Polynomial.equalEndpoint`.
This source façade records the two Stacks references that use it.
-/

@[expose] public section

@[stacks 00F1 "equal-endpoint polynomial algebra"]
#check @Polynomial.equalEndpoint

@[stacks 00JG "membership in the equal-endpoint polynomial algebra"]
#check @Polynomial.mem_equalEndpoint
