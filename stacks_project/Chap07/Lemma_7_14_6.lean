/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Criteria

import StacksCheckRecall

@[expose] public section

/-!
[stacks 00X5]

Lemma 7.14.6 is the filtered structured-arrow criterion for a continuous functor to define a
morphism of sites.
-/

@[stacks 00X5] #check CategoryTheory.IsMorphismOfSites.of_filteredStructuredArrow
