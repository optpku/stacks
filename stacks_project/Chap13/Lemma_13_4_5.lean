/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Endomorphism
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.5

The textbook `(0, b, 0)` formulation is the direct special case of the
middle-component composition API for distinguished triangle endomorphisms.
-/

@[stacks 05QP] #check @CategoryTheory.Pretriangulated.Triangle.Endomorphism.comp₂_eq_zero
