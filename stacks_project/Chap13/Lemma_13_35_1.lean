/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksCheckRecall

@[expose] public section

-- Lemma 13.35.1: associativity of the extension product is already owned by Mathlib.
@[stacks 0FX1] #check @CategoryTheory.ObjectProperty.extensionProduct_assoc
