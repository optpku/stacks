/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Coherent.Basic

@[expose] public section

/-!
# Noetherian Rings Are Coherent

@stack 05CY

The standard bridge from Noetherianity to coherence.
-/

universe u

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.90.5: a Noetherian ring is a coherent ring. -/
@[stacks 05CY]
instance noetherianRing_isCoherentRing [IsNoetherianRing R] : IsCoherentRing R := sorry

end
