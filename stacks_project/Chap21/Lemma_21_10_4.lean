/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Injectivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/- Lemma 21.10.4 (Tag 0A6G): for a covering family, the normalized degree-one Čech-to-site
cohomology comparison is injective, hence a monomorphism. -/

@[stacks 0A6G "injectivity of a degree-one Cech comparison"]
#check @CategoryTheory.cechCohomologyToSiteCohomology_injective_degree_one

#check @CategoryTheory.Cech.IsComparison.injective_degree_one
#check @CategoryTheory.Cech.IsComparison.mono_degree_one
