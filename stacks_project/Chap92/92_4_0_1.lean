/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_4_0_1_Morphism»
public import stacks_project.Chap92.«92_4_0_1_Polynomial»
import StacksCheckRecall

@[expose] public section

open CommAlgCat.Over.Polynomial
open CommAlgCat.Over.Polynomial.Site

/- 92.4.0.1 (1): the morphism of ringed topoi i : (Sh(C), underline{B}) ⟶ (Sh(C), O)
is the identity on underlying topoi, with i♯ : O ⟶ underline{B} the augmentations. -/
@[stacks 08PR]
#check CommAlgCat.Over.Polynomial.Site.i

/- 92.4.0.1 (2): the morphism of ringed topoi π : (Sh(C), underline{B}) ⟶ (Sh(*), B)
is the category-to-point morphism. -/
@[stacks 08PR]
#check CommAlgCat.Over.Polynomial.Site.toPoint
