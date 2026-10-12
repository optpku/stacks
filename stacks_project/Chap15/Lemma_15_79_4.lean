/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Quotient
import StacksCheckRecall

/-!
# Lemma 15.79.4 (07LU)

@stack 07LU

Perfectness descent across a nilpotent quotient is owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.79.4 (07LU): a complex is perfect if its derived reduction modulo a nilpotent ideal
is perfect. -/
@[stacks 07LU "Lemma 15.79.4"]
#check @isPerfect_of_derivedTensorWithAlgebra_quotient_isPerfect_of_isNilpotent
