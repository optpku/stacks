/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.IntegralClosure
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.56.3

The integral closure along a homomorphism of `ℕ`-graded rings is a graded subalgebra.

@stack 077G
-/

/- Lemma 10.56.3 (Tag 077G): if `R → S` is a homomorphism of `ℕ`-graded rings,
then the integral closure of `R` in `S` is a graded `R`-subalgebra of `S`. -/
@[stacks 077G]
#check @integralClosure.isHomogeneous

@[stacks 077G "underlying submodule"]
#check @integralClosure.toSubmodule_isHomogeneous
