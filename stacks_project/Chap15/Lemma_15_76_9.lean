/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.QuotientLifting
import StacksCheckRecall

/-!
# Lemma 15.76.9 (0BCE)

@stack 0BCE
-/

@[expose] public section

/- Lemma 15.76.9: bounded-above finite-projective representatives lift across a henselian
quotient, preserving termwise freeness. -/
@[stacks 0BCE "Lemma 15.76.9"]
#check @CategoryTheory.DerivedCategory.QuotientLifting.exists_finiteProjective
