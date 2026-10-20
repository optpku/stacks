/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian.Comparison
import StacksCheckRecall

@[expose] public section

/- Lemma 21.9.4 (Tag 03AT): positive-degree exactness of the fixed-target free-abelian Cech
complex. -/

@[stacks 03AT "fixed-target free-abelian Cech homology vanishing"]
#check @CategoryTheory.Cech.FreeAbelian.coverComplex_homology_isZero_succ

#check @CategoryTheory.Cech.FreeAbelian.coverComplex_homology_isZero_of_pos
