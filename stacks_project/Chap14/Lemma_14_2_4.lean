/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence
import StacksCheckRecall

/-!
@stack 0168
-/

@[expose] public section

open CategoryTheory

namespace SimplexCategoryGenRel

/- Lemma 14.2.4: the simplex category is presented by the coface and codegeneracy generators,
subject only to the simplicial identities. -/
@[stacks 0168]
#check (toSimplexCategory.isEquivalence : toSimplexCategory.IsEquivalence)

/- The reusable theorem is registered as the canonical equivalence instance. -/
#check (inferInstance : toSimplexCategory.IsEquivalence)

end SimplexCategoryGenRel
