/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.99.13 support index

The reusable categorical surjectivity step is owned directly by Mathlib.

@stack 00MN
-/

@[stacks 00MN "epimorphic cycles comparison gives epimorphic homology"]
#check @CategoryTheory.ShortComplex.epi_homologyMap_of_epi_cyclesMap'
