/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.Local
import StacksCheckRecall

/-!
# Lemma 61.4.6

An ind-Zariski ring map identifies local rings.
-/

@[expose] public section

universe u

/- Lemma 61.4.6: if a ring map `A → B` is ind-Zariski, then `A → B` identifies
local rings. -/
@[stacks 096T] #check
  (RingHom.IndZariski.isIsoOnLocalRings :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      {f : R →+* A}, f.IndZariski → f.IsIsoOnLocalRings)
