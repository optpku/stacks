/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Oka.Disjoint
import StacksCheckRecall

/-!
# Example 10.28.3

@stack 05KA
-/

@[expose] public section

@[stacks 05KA "ideals meeting a submonoid form an Oka family"]
#check @Ideal.isOka_not_disjoint
