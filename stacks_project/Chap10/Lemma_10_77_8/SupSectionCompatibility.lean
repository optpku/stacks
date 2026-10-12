/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Projective.Pullback
public import ReasLib.LinearAlgebra.Quotient.Pair
public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.Patching
import StacksCheckRecall

/-!
# Compatibility of quotient sections for Lemma 10.77.8

The compatibility condition is the generic paired-quotient range condition; projective lifting is
supplied by the standard module API.

@stack 0H7M
-/

@[expose] public section

@[stacks 0H7M "compatibility modulo a submodule sum"]
#check @Submodule.Quotient.mem_range_pairMap_iff

@[stacks 0H7M "quotient transition on representatives"]
#check @Submodule.factor_mk

@[stacks 0H7M "quotient transition surjectivity"]
#check @Submodule.factor_surjective

@[stacks 0H7M "compatible projective right inverse"]
#check @LinearMap.Pullback.exists_compatible_rightInverse
