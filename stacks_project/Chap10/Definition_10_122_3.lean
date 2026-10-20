/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.QuasiFinite.FiniteType
import StacksCheckRecall

/-!
# Definition 10.122.3

@stack 00PL
-/

@[expose] public section

/- Definition 10.122.3 (Stacks tag `00PL`) is the finite-type refinement of Mathlib's
finite-fiber quasi-finiteness. The canonical owner is
`Algebra.FiniteType.QuasiFinite` (and its primewise form
`Algebra.FiniteType.QuasiFiniteAt`) in `ReasLib.RingTheory.QuasiFinite.FiniteType`; it preserves
the finite-type hypothesis that Mathlib's `Algebra.QuasiFinite` intentionally does not carry. -/
@[stacks 00PL "(1)"]
#check @Algebra.FiniteType.QuasiFiniteAt
@[stacks 00PL "(2)"]
#check @Algebra.FiniteType.QuasiFinite
