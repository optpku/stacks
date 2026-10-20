/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Coherent.Countable

@[expose] public section

universe u

/- Lemma 110.12.3: a countable commutative ring `R` is coherent if and only if
the countable power `ℕ → R` is a flat `R`-module. -/
@[stacks 0ALB] #check
  (IsCoherentRing.iff_piNat_flat :
    ∀ {R : Type u} [CommRing R] [Countable R],
      IsCoherentRing R ↔ Module.Flat R (ℕ → R))
