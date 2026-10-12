/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.InverseSystem.TailBiproduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.42.1

For a directed preorder-indexed inverse system in a pretriangulated category,
essential constancy is equivalent to a tailwise biproduct decomposition into a
fixed summand and an eventually-zero complementary inverse system.
-/

@[stacks 0G39] #check @CategoryTheory.IsCofiltered.IsEssentiallyConstant.iff_hasTailBiproductDecomposition

#check @CategoryTheory.PreorderInverseSystem.tail
#check @CategoryTheory.PreorderInverseSystem.HasTailBiproductDecomposition
