/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.StableFree.ShortExact

@[expose] public section

/-!
# Lemma 15.3.2 (0BC4)

@stack 0BC4
-/

-- Lemma 15.3.2 (1): stable freeness of the outer terms implies it for the middle term.
@[stacks 0BC4 "Lemma 15.3.2 (1)"]
#check @CategoryTheory.ShortComplex.ShortExact.stablyFree_X₂

-- Lemma 15.3.2 (2): stable freeness of the source and middle terms implies it for the target.
@[stacks 0BC4 "Lemma 15.3.2 (2)"]
#check @CategoryTheory.ShortComplex.ShortExact.stablyFree_X₃

-- Lemma 15.3.2 (3): stable freeness of the middle and target terms implies it for the source.
@[stacks 0BC4 "Lemma 15.3.2 (3)"]
#check @CategoryTheory.ShortComplex.ShortExact.stablyFree_X₁
