/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.SumFactorization
import StacksCheckRecall

/-!
# Example 10.136.7

@stack 00SQ
-/

@[expose] public section

namespace MvPolynomial

variable (n m : ℕ)

@[stacks 00SQ "generic factorization map"]
#check (SumFactorization.map ℤ n m)

@[stacks 00SQ "generic monic factorization identity"]
#check (SumFactorization.map_freeMonic ℤ n m)

@[stacks 00SQ "relative global complete intersection"]
#check (SumFactorization.isRelativeGlobalCompleteIntersection ℤ n m)

@[stacks 00SQ "finite generic factorization map"]
#check (SumFactorization.map_finite ℤ n m)

end MvPolynomial
