/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived.Model
import StacksCheckRecall

/-!
Lemma 21.53.1 (094G): a bounded derived object whose cohomology sheaves are finite-type locally
constant admits, over a cover of the terminal object, bounded complex models with finite-type
locally constant terms. The reusable owner also provides the stronger arbitrary-object form.
-/

@[expose] public section

open CategoryTheory

@[stacks 094G]
#check @CategoryTheory.Sheaf.DerivedRestriction.exists_cover_model_terminal

#check @CategoryTheory.Sheaf.DerivedRestriction.HasBoundedFiniteTypeLocallyConstantModelOn
#check @CategoryTheory.Sheaf.DerivedRestriction.hasBoundedFiniteTypeLocallyConstantModelOn_iff
#check @CategoryTheory.Sheaf.DerivedRestriction.exists_cover_model

end
