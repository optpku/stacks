/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.DerivedTensor
import StacksCheckRecall

/-!
Lemma 21.53.4 (tag `094H`).  For a Noetherian coefficient ring, finite-type locally constant
cohomology is closed under derived tensor products of bounded-above objects.  The reusable owner
uses the canonical `DerivedCategory.cohomologyIn` predicate and `t.minus` membership.
-/

@[expose] public section

open CategoryTheory

@[stacks 094H]
#check @CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology.tensor

#check @CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology.tensor_of_isLE
#check @CategoryTheory.Sheaf.finiteTypeLocallyConstantModule
#check @CategoryTheory.DerivedCategory.cohomologyIn

end
