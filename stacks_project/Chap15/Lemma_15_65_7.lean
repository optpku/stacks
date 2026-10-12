/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Vanishing
import StacksCheckRecall

/-!
# Homology-vanishing criteria

Lemma 15.65.7 is a direct source-facing recall of the three atomic criteria in
`CochainComplex.isMPseudoCoherent_of_homology_isZero_*`.  The owner keeps the homology objects and
their finiteness assumptions explicit, so later proofs can reuse each clause independently.

@stack 064W
-/

@[expose] public section

/- Lemma 15.65.7 (1). -/
@[stacks 064W "(1), vanishing above and at m"]
#check @CategoryTheory.CochainComplex.isMPseudoCoherent_of_homology_isZero_ge

/- Lemma 15.65.7 (2). -/
@[stacks 064W "(2), finite top homology"]
#check @CategoryTheory.CochainComplex.isMPseudoCoherent_of_homology_isZero_gt_and_finite

/- Lemma 15.65.7 (3). -/
@[stacks 064W "(3), finite top and next homology"]
#check @CategoryTheory.CochainComplex.isMPseudoCoherent_of_homology_isZero_gt_add_one_and_finite

#print axioms CategoryTheory.CochainComplex.isMPseudoCoherent_of_homology_isZero_ge
#print axioms CategoryTheory.CochainComplex.isMPseudoCoherent_of_homology_isZero_gt_and_finite
#print axioms CategoryTheory.CochainComplex.isMPseudoCoherent_of_homology_isZero_gt_add_one_and_finite
