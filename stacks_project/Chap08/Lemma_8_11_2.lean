/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Equivalence
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.11.2: equivalences of categories over the base preserve and reflect the gerbe
condition.  The shared owner is stated for arbitrary projection functors, so no stack-specific
wrapper or chosen inverse is exposed here. -/
@[stacks 06P0]
#check @IsGerbe.iff_of_isEquivalence

/- The forward transport direction is available independently for downstream constructions. -/
#check @IsGerbe.of_isEquivalence

end CategoryTheory
