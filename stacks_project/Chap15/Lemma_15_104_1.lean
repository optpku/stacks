/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
import Mathlib.Algebra.Category.Grp.Abelian
import StacksCheckRecall

/-!
# Lemma 15.104.1

The source statement is the diagonal-acyclicity specialization of the reusable product-total API.

@stack 0H0Q
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex₂

noncomputable section

open scoped HomologicalComplex₂

/- Lemma 15.104.1 (0H0Q): for a complex of complexes of abelian groups, if the `p`-th column has
zero homology in degree `-p`, then the associated product total has zero homology in degree `0`.
The owner is stated for an abelian category with exact countable products and this check records the
source specialization `C := AddCommGrpCat`. -/
@[stacks 0H0Q "diagonal acyclicity for a product total"]
#check @HomologicalComplex₂.CoaugmentedResolution.ProductTotal.isZero_homology_zero_of_diagonal
@[stacks 0H0Q "abelian-group specialization of diagonal acyclicity"]
#check @HomologicalComplex₂.CoaugmentedResolution.ProductTotal.isZero_homology_zero_of_diagonal
  (C := AddCommGrpCat)
