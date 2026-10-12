/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.Patching
import StacksCheckRecall

/-!
# Quotient free-cover support for Lemma 10.77.8

The proof uses only canonical free covers, induced quotient maps, and the projective lifting
property. No chapter-local construction is part of the reusable API.

@stack 0H7M
-/

@[expose] public section

@[stacks 0H7M "canonical free cover"]
#check @Finsupp.linearCombination_surjective

@[stacks 0H7M "surjectivity of induced quotient maps"]
#check @Submodule.mapQ_surjective_of_surjective

@[stacks 0H7M "surjectivity criterion for ideal quotient maps"]
#check @LinearMap.quotientMapByIdeal_surjective_iff

@[stacks 0H7M "projective lifting across a surjective linear map"]
#check @LinearMap.exists_rightInverse_of_surjective

@[stacks 0H7M "canonical quotient factor representative"]
#check @Submodule.factor_mk

@[stacks 0H7M "quotient factor surjectivity"]
#check @Submodule.factor_surjective
