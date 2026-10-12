/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Subcategory.Orthogonal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.40.6

The dual owner-level statement is the canonical triangulated-instance closure
of `extensionProduct A.leftOrthogonal A`; its clausewise source formulation is
recovered through the standard `ObjectProperty.IsTriangulated` consequences.
-/

@[stacks 0H0N] #check @CategoryTheory.ObjectProperty.leftOrthogonal_extensionProduct_isTriangulated
