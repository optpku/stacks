/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.QuotientLifting
import StacksCheckRecall

/-!
# Lemma 15.76.3 (09AR)

@stack 09AR
-/

@[expose] public section

/- Lemma 15.76.3: bounded-above projective representatives lift across a nilpotent quotient. -/
@[stacks 09AR "Lemma 15.76.3"]
#check @CategoryTheory.DerivedCategory.QuotientLifting.exists_projective
