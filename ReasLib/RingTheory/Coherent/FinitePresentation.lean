/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Coherent.Operations

@[expose] public section

/-!
# Coherence and Finite Presentation

@stack 05CX

The finite-presentation characterization over a coherent ring.
-/

universe u v

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.90.4: over a coherent ring, an `R`-module is coherent if and only if it is finitely
presented. -/
@[stacks 05CX]
theorem module_coherent_iff_finitePresentation [Module.Coherent R R] :
    Module.Coherent R M ↔ Module.FinitePresentation R M := sorry

end
