/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.NoetherianDescent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.138.14

@stack 00TP
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.138.14: a smooth `R`-algebra admits a smooth model over a finitely generated
`ℤ`-subalgebra of `R`; using `Subalgebra.fg_iff_finiteType`, this is the book's finite-type
integer-subalgebra model statement. This is exactly the canonical theorem
`Algebra.Smooth.exists_subalgebra_fg`. -/
@[stacks 00TP]
#check @Algebra.Smooth.exists_subalgebra_fg
