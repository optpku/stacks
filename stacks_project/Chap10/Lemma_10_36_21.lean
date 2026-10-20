/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.36.21 (Tag 05DR): finite ring maps have finite fibers on prime spectra.

@stack 05DR
-/

@[stacks 05DR "finite maps are quasi-finite"]
#check @RingHom.QuasiFinite.of_finite

@[stacks 05DR "quasi-finite maps have finite spectrum fibers"]
#check @Algebra.QuasiFinite.finite_comap_preimage_singleton
