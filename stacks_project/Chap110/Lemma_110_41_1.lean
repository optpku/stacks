/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Counterexample.NonFlat
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.41.1 -/
@[stacks 057W]
#check (RingHom.exists_formallySmooth_not_flat :
  ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
    f.FormallySmooth ∧ ¬ f.Flat)
