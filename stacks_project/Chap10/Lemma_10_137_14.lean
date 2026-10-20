/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Pi

@[expose] public section

/-!
@stack 0GIF
-/

/-!
# Smoothness of Products Recall

The finite-family shared API is the canonical owner.  This item recalls its
binary specialization.
-/

/- Lemma 10.137.14, tag 0GIF: a product `R`-algebra `S' × S''` is smooth over
`R` if and only if both factors are smooth over `R`. -/
@[stacks 0GIF "smoothness of binary products"]
#check @Algebra.Smooth.prod_iff
