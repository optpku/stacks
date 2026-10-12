/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Matrix
public import Mathlib.LinearAlgebra.Matrix.Ideal
import StacksCheckRecall

@[expose] public section

/- Lemma 11.4.5 (1): for every nonempty full matrix ring, the category of right modules is
equivalent to the category of right modules over that matrix ring.  The reusable owner is
`ModuleCat.matrixRightEquivalence`; its explicit index parameter records the choice needed for
the inverse Morita functor. -/
@[stacks 074D]
recall ModuleCat.matrixRightEquivalence

/- Lemma 11.4.5 (2): two-sided ideals of `R` and of `Matrix ι ι R` correspond through the
canonical matrix-ideal equivalence. -/
recall TwoSidedIdeal.equivMatrix

/- Lemma 11.4.5 (3): the center of a full matrix ring is the scalar-matrix image of the center
of its coefficient ring. -/
recall Matrix.subringCenter_eq_scalar_map
