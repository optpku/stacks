/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocalSquare
import StacksCheckRecall

/-!
# Flat base change in a local square

@stack 0GEB
-/

@[expose] public section

/- Lemma 10.100.2: flat base change in a commutative square of local homomorphisms, under the
maximal-ideal extension and Noetherian hypotheses. -/
@[stacks 0GEB]
#check @Module.Flat.LocalSquare.baseChange_of_maximalIdeal_eq
