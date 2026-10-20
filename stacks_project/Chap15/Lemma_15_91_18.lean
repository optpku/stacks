/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleProperties
import StacksCheckRecall

/-!
# Flatness over a Beauville--Laszlo glueing pair

The reusable owner states the criterion for an explicit ring homomorphism;
its target-side tensor product is the canonical `S ⊗[R] M` orientation.

@stack 0BP7
-/

/- Lemma 15.91.18 (0BP7): an `R`-module is flat if and only if its base
change to the target ring and its localization away from `f` are flat. -/
@[stacks 0BP7 "Lemma 15.91.18"]
#check @LocalizedModule.Away.BeauvilleLaszlo.flat_iff_baseChange_and_localizedAway_of_glueingPair
