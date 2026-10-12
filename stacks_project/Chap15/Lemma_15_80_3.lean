/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Regular.HomologyGap
import StacksCheckRecall

/-!
# Lemma 15.80.3 (0FXJ)

@stack 0FXJ
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.80.3 (0FXJ): a sufficiently wide cohomology gap over a finite-dimensional regular
ring forces morphism vanishing. -/
@[stacks 0FXJ "Lemma 15.80.3"]
#check @hom_eq_zero_of_boundedAbove_of_homology_gap_over_regularRing
