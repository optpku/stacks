/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ProductRange.SplittingLocus
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.97.7

@stack 0F80
-/

/-!
# Lemma 15.97.7

The reusable owner is `LinearMap.ProductRange.exists_fgIdeal`.  Its hypotheses retain the source
assumption that the source and both target factors are finite projective modules; the weaker
finite-source theorem is available as `LinearMap.ProductRange.exists_fgIdeal_of_finite_source`.
-/

-- Lemma 15.97.7: a finitely generated ideal universally cuts out the product-splitting locus.
@[stacks 0F80 "product-splitting locus of a split injection"]
#check @LinearMap.ProductRange.exists_fgIdeal
