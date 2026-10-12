/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Quotient.Pair
import StacksCheckRecall

/-!
# Compatible pairs of quotient classes

Source-facing recall for the fibre-product step in Lemma 10.77.8.

@stack 0H7M
-/

@[expose] public section

@[stacks 0H7M "paired quotient map"]
#check @Submodule.Quotient.pairMap

@[stacks 0H7M "compatible quotient pairs"]
#check @Submodule.Quotient.compatiblePairs

@[stacks 0H7M "paired quotient range"]
#check @Submodule.Quotient.range_pairMap

@[stacks 0H7M "compatible pair criterion"]
#check @Submodule.Quotient.mem_range_pairMap_iff

@[stacks 0H7M "paired quotient map into compatible pairs"]
#check @Submodule.Quotient.compatiblePairMap

@[stacks 0H7M "common representative for compatible pairs"]
#check @Submodule.Quotient.compatiblePairMap_surjective

@[stacks 0H7M "paired quotient equivalence"]
#check @Submodule.Quotient.compatiblePairsEquiv
