/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism.Adjoint

import StacksCheckRecall

@[expose] public section

/-!
[stacks 09YX]

Lemma 7.24.1 is the local-corepresentability criterion for an inverse image to admit a left
adjoint, expressed through a covering family of generators.
-/

#check CategoryTheory.MorphismOfTopoiIn.hasCorepresentableSectionsOn
@[stacks 09YX] #check CategoryTheory.MorphismOfTopoiIn.isRightAdjoint_of_corepresentableSections
