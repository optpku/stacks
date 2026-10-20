/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.83.2

Faithfully flat base change detects finite generation, finite presentation, and flatness of
modules.  The first and third clauses are Mathlib recalls; the finite-presentation owner lives in
`ReasLib.Algebra.Module.FinitePresentation.Descent`.

@stack 03C4
-/

/- Lemma 10.83.2 (1): finite generation descends along faithfully flat base change. -/
@[stacks 03C4 "(1)"]
#check @Module.Finite.of_finite_tensorProduct_of_faithfullyFlat

/- Lemma 10.83.2 (2): finite presentation descends along faithfully flat base change. -/
@[stacks 03C4 "(2)"]
#check @Module.FinitePresentation.of_tensorProduct_of_faithfullyFlat

/- Lemma 10.83.2 (3): flatness descends along faithfully flat base change. -/
@[stacks 03C4 "(3)"]
#check @Module.Flat.of_flat_tensorProduct
