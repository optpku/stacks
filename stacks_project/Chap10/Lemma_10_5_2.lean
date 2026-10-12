/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Projective.Range
import StacksCheckRecall

/-!
# Projective factorization through a containing range

@stack 07JX
-/

@[expose] public section

@[stacks 07JX "projective range-factorization owner"]
#check @LinearMap.exists_comp_eq_of_range_le

@[stacks 07JX "range inclusion characterized by factorization"]
#check @LinearMap.range_le_iff_exists_comp
