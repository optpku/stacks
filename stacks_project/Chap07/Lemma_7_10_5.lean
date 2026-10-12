/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Covering

import StacksCheckRecall

@[expose] public section

/-!
[stacks 00W6]

Lemma 7.10.5 is the common-covering-refinement property of fixed-target families.
-/

@[stacks 00W6] #check CategoryTheory.SemiRepresentableFamily.Over.existsCommonCoveringRefinement
