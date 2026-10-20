/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Completion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.7

Existence of a distinguished completion is Mathlib's general construction;
the ReasLib bridge retains the source's fixed-first-morphism comparison in a
reusable form.
-/

@[stacks 014B] #check @CategoryTheory.Pretriangulated.distinguished_cocone_triangle

@[stacks 014B] #check @CategoryTheory.Pretriangulated.Triangle.existsIsoOfSameMor₁
