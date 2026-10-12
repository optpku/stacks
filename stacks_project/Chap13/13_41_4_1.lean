/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.IntFamily
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.41.4.1

The successor-diagonal shifted-Hom condition is generic, while the finite-row
integer-indexed views are supplied by the Postnikov-system support leaf.
-/

@[stacks 0DW1] #check @CategoryTheory.ShiftedHom.vanishesAboveSuccessor

#check @CategoryTheory.ComposableArrows.intFamily
#check @CategoryTheory.PostnikovSystem.intFamily
