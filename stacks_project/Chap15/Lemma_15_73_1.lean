/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Duality.Module
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.73.1

@stack 0FNJ
-/

/-!
# Exact pairings of modules

Lemma 15.73.1 (0FNJ) is the module specialization of the canonical exact-pairing API.  For an
explicit `p : ExactPairing M N`, both members are finite projective, and the coevaluation formula
identifies `Module.Dual R M` with the chosen left dual `N`.  The reusable declarations live in
`ReasLib.CategoryTheory.Monoidal.Duality.Module`.
-/

@[stacks 0FNJ "(1)"] #check @CategoryTheory.ExactPairing.left_finiteProjective
@[stacks 0FNJ "(1)"] #check @CategoryTheory.ExactPairing.right_finiteProjective
@[stacks 0FNJ "(2)"] #check @CategoryTheory.ExactPairing.moduleDualIso
@[stacks 0FNJ "(2)"] #check @CategoryTheory.ExactPairing.fromModuleDual
@[stacks 0FNJ "(2)"] #check @CategoryTheory.ExactPairing.fromModuleDual_apply
@[stacks 0FNJ "(3)"] #check @CategoryTheory.ExactPairing.toModuleDual
@[stacks 0FNJ "(3)"] #check @CategoryTheory.ExactPairing.toModuleDual_apply
