/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.LowLength.Nonexistence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.41.3

The positive low-length assertions and the two lengthwise non-universality assertions are neutral
finite-Postnikov-system API. The shared predicates keep ambient-category quantification out of
downstream statements.
-/

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.nonempty_zero

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.Morphism.nonempty_zero

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.Morphism.subsingleton_zero

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.nonempty_one

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.Morphism.nonempty_one

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.nonempty_two

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.ExistsAtLength

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.Morphism.ExtendsAtLength

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.Morphism.ExtendsAtLength.not_forall_two

@[stacks 0D81] #check @CategoryTheory.PostnikovSystem.ExistsAtLength.not_forall_of_two_lt
