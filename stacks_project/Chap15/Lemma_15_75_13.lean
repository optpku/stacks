/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.FaithfullyFlat
import StacksCheckRecall

/-!
# Lemma 15.75.13

@stack 068T

The canonical descent and iff owners keep the ring homomorphism and faithfully flat hypothesis
explicit.
-/

@[expose] public section

open CategoryTheory

@[stacks 068T "Lemma 15.75.13"]
#check @DerivedCategory.IsPerfect.of_faithfullyFlat

#check @DerivedCategory.IsPerfect.extension_iff_of_faithfullyFlat
