/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Products
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.12 (060L): objectwise sheaf cohomology commutes with arbitrary products in
degree zero, and its product comparison is injective in degree one. -/
@[stacks 0D0A "Lemma 20.11.12: degree-zero product comparison"]
#check @CategoryTheory.Sheaf.Cohomology.productComparison_isIso_zero

@[stacks 0D0A "Lemma 20.11.12: degree-one product comparison"]
#check @CategoryTheory.Sheaf.Cohomology.productComparison_injective_one
