/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.LeftInverse
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.15.5

@stack 07DQ

Maximal-minor ideals and scalar left inverses are owned by `Matrix.MinorIdeal`; no `Fin`-specific
chapter wrapper is needed.
-/

/- Lemma 10.15.5 (1): membership in the maximal-minor ideal produces a scalar left inverse. -/
@[stacks 07DQ "maximal-minor left inverse"]
#check @Matrix.MinorIdeal.exists_mul_eq_smul_one

/- Lemma 10.15.5 (2): a scalar left inverse puts the corresponding power in the maximal-minor
ideal. -/
@[stacks 07DQ "maximal-minor power criterion"]
#check @Matrix.MinorIdeal.pow_mem_of_mul_eq_smul_one

/- Existential form of the second source clause. -/
#check @Matrix.MinorIdeal.pow_mem_of_exists_mul_eq_smul_one

end
