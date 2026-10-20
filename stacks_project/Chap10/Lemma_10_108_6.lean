/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.Generalization
import StacksCheckRecall

/-!
# Finite Flat Modules and Generalization-Stable Closed Subsets

@stack 052U
-/

@[expose] public section

/- Lemma 10.108.6 (052U): every closed subset of `Spec(R)` stable under
generalization is open if and only if every finite flat `R`-module is finite
locally free. -/
@[stacks 052U "finite flat / finite locally free criterion"]
#check @PrimeSpectrum.closed_stableUnderGeneralization_isOpen_iff_finiteFlat_finiteLocallyFree
