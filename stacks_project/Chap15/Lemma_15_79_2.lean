/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Colimit.Sequential.RepresentedHom
import StacksCheckRecall

/-!
# Lemma 15.79.2 (07LR)

@stack 07LR

The concrete comparison map and its isomorphism criterion are owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.79.2 (07LR): represented Hom preserves the canonical sequential-colimit comparison
when it preserves countable coproducts. -/
@[stacks 07LR "Lemma 15.79.2"]
#check @DerivedCategory.compactSequentialHomComparison_isIso

#check @DerivedCategory.compactSequentialHomComparison

#print axioms DerivedCategory.compactSequentialHomComparison
