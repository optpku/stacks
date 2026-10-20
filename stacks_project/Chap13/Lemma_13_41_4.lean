/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Extension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.41.4

Successor-diagonal shifted-Hom vanishing transfers to auxiliary objects and
then extends any finite-row morphism to a morphism of Postnikov systems.
-/

@[stacks 0D82] #check @CategoryTheory.PostnikovSystem.vanishesAboveSuccessor_auxiliary

@[stacks 0D82] #check @CategoryTheory.PostnikovSystem.Morphism.nonempty_of_vanishesAboveSuccessor
