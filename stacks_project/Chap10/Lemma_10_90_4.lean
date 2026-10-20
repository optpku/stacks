/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Coherent.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.90.4

@stack 05CX
-/

/-!
# Chapter 10 Compatibility Facade

Lemma 10.90.4 is the finite-presentation characterization in the neutral coherent-module API.
-/

/- Lemma 10.90.4 (Tag 05CX): over a coherent ring, `Module.Coherent R M` is equivalent to
`Module.FinitePresentation R M`. -/
@[stacks 05CX]
#check @module_coherent_iff_finitePresentation
