/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.DimensionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Finite-type dimension formula

The canonical library owners are the bundled prime-spectrum formulas in
`PrimeSpectrum`; the explicit lying-over ideal presentation is obtained by
rewriting the contraction of the selected prime.

@stack 02IJ
-/

/- Lemma 10.113.1 (1): the finite-type dimension inequality. -/
@[stacks 02IJ "(1)"]
#check @PrimeSpectrum.height_add_residueFieldTrdeg_le_of_finiteType

/- Lemma 10.113.1 (2): universal catenarity upgrades the inequality to an equality. -/
@[stacks 02IJ "(2)"]
#check @PrimeSpectrum.height_add_residueFieldTrdeg_eq_of_universallyCatenary
