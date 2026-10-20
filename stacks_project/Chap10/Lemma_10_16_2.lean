/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.16.2

@stack 05BT
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.16.2: let `R` be a ring, let `M` be a finite `R`-module, and let `φ : M → M` be an
endomorphism. Then there exists a monic polynomial over `R` that annihilates `φ`. This is exactly
the canonical finite-module Cayley-Hamilton theorem
`LinearMap.exists_monic_and_aeval_eq_zero`. -/
@[stacks 05BT]
#check @LinearMap.exists_monic_and_aeval_eq_zero
